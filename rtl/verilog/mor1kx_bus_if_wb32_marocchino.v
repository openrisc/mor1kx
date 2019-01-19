////////////////////////////////////////////////////////////////////////
//                                                                    //
//  mor1kx_bus_if_wb32_marocchino                                     //
//                                                                    //
//  Description: mor1kx CPU <-> Wishbone IBUS/DBUS bridges            //
//               with Pseudo CDC (clock domain crossing)              //
//                                                                    //
//    (a) Assumes 32-bit data and address.                            //
//    (b) Only CLASSIC and B3_REGISTERED_FEEDBACK modes               //
//        are implemented                                             //
//    (c) Pseudo CDC disclaimer:                                      //
//        As positive edges of wb-clock and cpu-clock assumed be      //
//        aligned, we use simplest clock domain pseudo-synchronizers. //
//    (d) Also atomic reservation implemeted here in Wishbone         //
//        clock domain                                                //
//                                                                    //
////////////////////////////////////////////////////////////////////////
//                                                                    //
//   Copyright (C) 2017-2018 Andrey Bacherov                          //
//                           avbacherov@opencores.org                 //
//                                                                    //
//      This Source Code Form is subject to the terms of the          //
//      Open Hardware Description License, v. 1.0. If a copy          //
//      of the OHDL was not distributed with this file, You           //
//      can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt       //
//                                                                    //
////////////////////////////////////////////////////////////////////////

`include "mor1kx-defines.v"

module mor1kx_bus_if_wb32_marocchino
#(
  parameter DRIVER_TYPE         = "D_CACHE", // D_CACHE / I_CACHE
  parameter BUS_IF_TYPE         = "B3_REGISTERED_FEEDBACK", // CLASSIC / B3_REGISTERED_FEEDBACK
  parameter BURST_LENGTH        = 8,
  parameter OPTION_DCACHE_SNOOP = "NONE" // for multi-core
)
(
  // Wishbone side clock and reset
  input             wb_clk,
  input             wb_rst,

  // CPU side clock and reset
  input             cpu_clk,
  input             cpu_rst,
  // For lwa/swa
  input             pipeline_flush_i,

  // CPU side
  output reg        cpu_err_o,
  output reg        cpu_ack_o,
  output reg [31:0] cpu_dat_o,
  output reg        cpu_burst_last_o,
  input      [31:0] cpu_adr_i,
  input      [31:0] cpu_dat_i,
  input             cpu_req_i,
  input       [3:0] cpu_bsel_i,
  input             cpu_lwa_cmd_i,
  input             cpu_stna_cmd_i,
  input             cpu_swa_cmd_i,
  input             cpu_burst_i,
  // Other connections for lwa/swa support
  output            cpu_atomic_flg_o,
  // For DCACHE snoop-invalidate
  output     [31:0] cpu_snoop_adr_o,
  output            cpu_snoop_en_o,

  // Wishbone side
  output     [31:0] wbm_adr_o,
  output            wbm_stb_o,
  output            wbm_cyc_o,
  output      [3:0] wbm_sel_o,
  output            wbm_we_o,
  output      [2:0] wbm_cti_o,
  output      [1:0] wbm_bte_o,
  output     [31:0] wbm_dat_o,
  input             wbm_err_i,
  input             wbm_ack_i,
  input      [31:0] wbm_dat_i,
  input             wbm_rty_i,
  // For lwa/swa
  input      [31:0] snoop_adr_i,
  input             snoop_en_i
);

  generate
  if (((BUS_IF_TYPE != "CLASSIC") && (BUS_IF_TYPE != "B3_REGISTERED_FEEDBACK")) ||
      ((DRIVER_TYPE != "D_CACHE") && (OPTION_DCACHE_SNOOP != "NONE"))) begin
    initial begin
      $display("ERROR: Incorrect configuration of a Wishbone bridge");
      $finish;
    end
  end
  endgenerate


  localparam [1:0] BTE_ID = (BURST_LENGTH ==  4) ? 2'b01 :
                            (BURST_LENGTH ==  8) ? 2'b10 :
                            (BURST_LENGTH == 16) ? 2'b11 :
                                                   2'b00; // Linear burst


  //----------------------------------------------//
  // Forward declarations for l.lwa/l.swa support //
  //----------------------------------------------//
  //
  // Cross connections for various generated blocks
  // All of them are in Wishbone clock domain
  //
  // CPU request clarifications
  // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  // !!! Use them only with "and" with another flags     !!!
  // !!! because they keep states between CPU's requests !!!
  // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  //
  wire        lwa_cmd;
  wire        stna_cmd;
  wire        swa_cmd;
  //
  // atomic reservation flag
  //
  wire        atomic_flg;
  //
  // Locally used snoop event attributes.
  //
  wire        snoop_en_l;  // latched snoop event flag
  wire [29:0] snoop_adr_l; // latched [31:2] of snooped address
  //
  // Locally generated DCACHE Snoop invalidation ACK
  //
  wire        cpu_snoop_inv_ack;


  //-------------------------//
  // CPU-toggle -> WBM-pulse //
  //-------------------------//
  //
  // Pseudo CDC disclaimer:
  // As positive edges of wb-clock and cpu-clock assumed be aligned,
  // we use simplest clock domain pseudo-synchronizers.
  //
  reg   cpu_req_r1;
  reg   cpu_req_r2;
  wire  cpu_req_pulse; // 1-clock in Wishbone clock domain
  // ---
  always @(posedge wb_clk) begin
    if (wb_rst) begin
      cpu_req_r2 <= 1'b0;
      cpu_req_r1 <= 1'b0;
    end
    else begin
      cpu_req_r2 <= cpu_req_r1;
      cpu_req_r1 <= cpu_req_i;
    end
  end // @wb-clock
  // ---
  assign cpu_req_pulse = cpu_req_r1 ^ cpu_req_r2;

  //
  // Wishbone domain lathes for CPU's requests
  // for both IBUS and DBUS bridges
  //
  reg  [31:0] cpu_adr_r1;
  reg  [31:0] cpu_dat_r1;
  reg   [3:0] cpu_bsel_r1;
  reg         cpu_burst_r1;
  // ---
  always @(posedge wb_clk) begin
    cpu_adr_r1   <= cpu_adr_i;
    cpu_dat_r1   <= cpu_dat_i;
    cpu_bsel_r1  <= cpu_bsel_i;
    cpu_burst_r1 <= cpu_burst_i;
  end // at wb-clock


  //----------------------------------------------------------//
  // CTI, BTE and reading burst support for IBUS/DBUS bridges //
  //----------------------------------------------------------//

  // Wishbone-clock domain registered control signals (to interconnect)
  reg  [2:0] to_wbm_cti_r;
  reg  [1:0] to_wbm_bte_r;

  // Wishbone-clock domain register address (to interconnect)
  reg [31:0] to_wbm_adr_r;

  // for burst control
  reg   [(BURST_LENGTH-1):0] burst_done_r;
  wire                       burst_proc;
  wire                       burst_keep;
  wire                [31:0] burst_next_adr;

  // continue busrting
  assign burst_proc = to_wbm_cti_r[1];
  assign burst_keep = burst_proc & (~burst_done_r[0]);

  // ---
  always @(posedge wb_clk) begin
    if (wb_rst) begin
      to_wbm_cti_r <=  3'd0;
      to_wbm_bte_r <=  2'd0;
      // for burst control
      burst_done_r <= {BURST_LENGTH{1'b0}};
    end
    else if (wbm_err_i) begin
      to_wbm_cti_r <=  3'd0;
      to_wbm_bte_r <=  2'd0;
      // for burst control
      burst_done_r <= {BURST_LENGTH{1'b0}};
    end
    else if (wbm_ack_i) begin
      to_wbm_cti_r <= (burst_proc ? (burst_done_r[1] ? 3'b111 : 3'b010) : 3'b000);
      to_wbm_bte_r <= burst_keep ? to_wbm_bte_r : 2'd0;
      // for burst control
      burst_done_r <= {1'b0, burst_done_r[(BURST_LENGTH-1):1]};
    end
    else if (cpu_req_pulse) begin // a bridge latches address and controls
      to_wbm_cti_r <= {1'b0, cpu_burst_r1, 1'b0}; // 010 if burst
      to_wbm_bte_r <= cpu_burst_r1 ? BTE_ID : 2'd0;
      // for burst control
      burst_done_r <= {cpu_burst_r1, {(BURST_LENGTH-1){1'b0}}};
    end
  end // @wb-clock


  // Wishbone-clock domain register address (to interconnect)
  // burst length is 8: 32 byte = (8 words x 32 bits/word) -> cache block length is 5
  // burst length is 4: 16 byte = (4 words x 32 bits/word) -> cache block length is 4
  assign burst_next_adr = (BURST_LENGTH == 8) ?
    {to_wbm_adr_r[31:5], to_wbm_adr_r[4:0] + 5'd4} : // 32 byte = (8 words x 32 bits/word)
    {to_wbm_adr_r[31:4], to_wbm_adr_r[3:0] + 4'd4};  // 16 byte = (4 words x 32 bits/word)
  // ---
  always @(posedge wb_clk) begin
    if (wbm_ack_i & burst_keep) begin // next burst address to Wishbone
      // pay attention:
      // as DCACHE is write through, "data" and "we" are irrelevant for read burst
      to_wbm_adr_r <= burst_next_adr;
    end
    else if (cpu_req_pulse) begin // start transaction : address
      to_wbm_adr_r <= cpu_adr_r1;
    end
  end // @wb-clock


  // --- IBUS/DBUS bridges output assignenment ---
  assign wbm_adr_o = to_wbm_adr_r; // IBUS/DBUS bridges
  assign wbm_cti_o = to_wbm_cti_r; // IBUS/DBUS bridges
  assign wbm_bte_o = to_wbm_bte_r; // IBUS/DBUS bridges


  //----------------------------------------------//
  // STB, CYC, WE, SEL, DAT for DBUS/IBUS bridges //
  //----------------------------------------------//

  reg  to_wbm_stb_r; // IBUS/DBUS bridges
  reg  to_wbm_cyc_r; // IBUS/DBUS bridges

  //
  // Here we declare states for DBUS control FSM
  // because some of EDA tools deprecate localparam
  // operator inside generate.
  //

  localparam [2:0] DBUS_WAITING_CPU_REQ = 3'b001,
                   DBUS_WAITING_WBM_ACQ = 3'b010,
                   DBUS_PENDING_WBM_REQ = 3'b100;

  generate
  /* verilator lint_off WIDTH */
  if (DRIVER_TYPE == "D_CACHE") begin: dbus_specific
  /* verilator lint_on WIDTH */

    // latch for command type
    reg  cpu_lwa_cmd_r1;
    reg  cpu_stna_cmd_r1;
    reg  cpu_swa_cmd_r1;

    // latch "CPU is requesting atomic operation" flag
    always @(posedge wb_clk) begin
      if (wb_rst) begin
        cpu_lwa_cmd_r1  <= 1'b0; // cpu-reset
        cpu_stna_cmd_r1 <= 1'b0; // cpu-reset
        cpu_swa_cmd_r1  <= 1'b0; // cpu-reset
      end
      else begin
        cpu_lwa_cmd_r1  <= cpu_lwa_cmd_i;  // taking cpu request
        cpu_stna_cmd_r1 <= cpu_stna_cmd_i; // taking cpu request
        cpu_swa_cmd_r1  <= cpu_swa_cmd_i;  // taking cpu request
      end
    end

    // CPU request clarifications
    assign lwa_cmd  = cpu_lwa_cmd_r1;  // DBUS bridge
    assign stna_cmd = cpu_stna_cmd_r1; // DBUS bridge
    assign swa_cmd  = cpu_swa_cmd_r1;  // DBUS bridge

    // For snoop event processing
    wire snoop_en_any = snoop_en_i | ((~cpu_snoop_inv_ack) & snoop_en_l); // DBUS bridge

    // DBUS request states
    reg  [2:0] dbus_state_r; // DBUS bridge
    // Byte select and write enable
    reg  [3:0] to_wbm_sel_r;
    reg        to_wbm_we_r;
    reg [31:0] to_wbm_dat_r;

    // --- STB, CYC and WE ---
    always @(posedge wb_clk) begin
      if (wb_rst) begin
        to_wbm_we_r  <= 1'b0;
        to_wbm_stb_r <= 1'b0; // DBUS bridge: reset
        to_wbm_cyc_r <= 1'b0; // DBUS bridge: reset
        dbus_state_r <= DBUS_WAITING_CPU_REQ;
      end
      else begin
        // synthesis parallel_case
        case (dbus_state_r)
          // waiting CPU request
          // l.swa could be "another l.swa" (i.e. to another location),
          // so we don't initiate DBUS request here, but do
          // "another l.swa" checking
          DBUS_WAITING_CPU_REQ: begin
            if (cpu_req_pulse) begin
              if (snoop_en_any) begin
                to_wbm_we_r  <= 1'b0;
                to_wbm_stb_r <= 1'b0; // DBUS bridge
                to_wbm_cyc_r <= 1'b0; // DBUS bridge
                dbus_state_r <= DBUS_PENDING_WBM_REQ;
              end
              else begin
                to_wbm_we_r  <= stna_cmd;
                to_wbm_stb_r <= (~swa_cmd); // DBUS bridge
                to_wbm_cyc_r <= (~swa_cmd); // DBUS bridge
                dbus_state_r <= swa_cmd ? DBUS_PENDING_WBM_REQ : DBUS_WAITING_WBM_ACQ;
              end
            end
          end

          // waiting DBUS ACK/ERR
          // for l.swa case we don't care about self-snoop because
          // DBUS ACK/ERR have more priority
          DBUS_WAITING_WBM_ACQ: begin
            if (wbm_err_i) begin
              to_wbm_we_r  <= 1'b0;
              to_wbm_stb_r <= 1'b0; // DBUS bridge
              to_wbm_cyc_r <= 1'b0; // DBUS bridge
              dbus_state_r <= DBUS_WAITING_CPU_REQ;
            end
            else if (wbm_ack_i) begin
              to_wbm_we_r  <= 1'b0; // DCACHE is write through, no write burst
              to_wbm_stb_r <= burst_keep; // DBUS bridge
              to_wbm_cyc_r <= burst_keep; // DBUS bridge
              dbus_state_r <= burst_keep ? DBUS_WAITING_WBM_ACQ : DBUS_WAITING_CPU_REQ;
            end
            else if (snoop_en_i) begin
              to_wbm_we_r  <= 1'b0;
              to_wbm_stb_r <= 1'b0; // DBUS bridge
              to_wbm_cyc_r <= 1'b0; // DBUS bridge
              dbus_state_r <= DBUS_PENDING_WBM_REQ;
            end
          end

          // pending request by l.swa or snoop-inv
          // (1) here we wait till completion of all snoop events
          // (2) if link has been broken while we was waiting here,
          //     the bus access is still performed as a (discarded) read.
          DBUS_PENDING_WBM_REQ: begin
            if (~snoop_en_any) begin
              to_wbm_we_r  <= stna_cmd | (swa_cmd & atomic_flg);
              to_wbm_stb_r <= 1'b1; // DBUS bridge
              to_wbm_cyc_r <= 1'b1; // DBUS bridge
              dbus_state_r <= DBUS_WAITING_WBM_ACQ;
            end
          end

          // don't change by default
          default:;
        endcase
      end
    end // @wb-clock

    // --- SEL & DATA for write ---
    always @(posedge wb_clk) begin
      to_wbm_sel_r <= cpu_bsel_r1;  // DBUS bridge
      to_wbm_dat_r <= cpu_dat_r1;   // DBUS bridge
    end // @wb-clock

    // --- DBUS bridge output assignenment ---
    assign wbm_stb_o = to_wbm_stb_r; // DBUS bridge
    assign wbm_cyc_o = to_wbm_cyc_r; // DBUS bridge
    assign wbm_we_o  = to_wbm_we_r;  // DBUS bridge
    assign wbm_sel_o = to_wbm_sel_r; // DBUS bridge
    assign wbm_dat_o = to_wbm_dat_r; // DBUS bridge

  end
  else begin : ibus_specific

    always @(posedge wb_clk) begin
      if (wb_rst) begin
        to_wbm_stb_r <= 1'b0; // IBUS bridge: reset
        to_wbm_cyc_r <= 1'b0; // IBUS bridge: reset
      end
      else if (wbm_err_i) begin
        to_wbm_stb_r <= 1'b0; // IBUS bridge
        to_wbm_cyc_r <= 1'b0; // IBUS bridge
      end
      else if (wbm_ack_i) begin
        to_wbm_stb_r <= burst_keep; // IBUS bridge
        to_wbm_cyc_r <= burst_keep; // IBUS bridge
      end
      else if (cpu_req_pulse) begin // rise CYC/STB in IBUS bridge
        to_wbm_stb_r <= 1'b1; // IBUS bridge
        to_wbm_cyc_r <= 1'b1; // IBUS bridge
      end
    end // @wb-clock

    // --- IBUS bridge output assignenment ---
    assign wbm_stb_o = to_wbm_stb_r;  // IBUS bridge
    assign wbm_cyc_o = to_wbm_cyc_r;  // IBUS bridge
    assign wbm_we_o  =  1'b0;         // IBUS bridge
    assign wbm_sel_o =  4'hf;         // IBUS bridge
    assign wbm_dat_o = 32'd0;         // IBUS bridge

  end
  endgenerate


  //------------//
  // WBM-to-CPU //
  //------------//

  // --- registered input controls (1-Wishbone-clock) ---
  reg         wbm_err_r;
  reg         wbm_ack_r;
  reg         wbm_burst_last_r;
  reg  [31:0] wbm_dat_r;
  // ---
  always @(posedge wb_clk) begin
    if (wb_rst) begin
      wbm_err_r        <= 1'b0;
      wbm_ack_r        <= 1'b0;
      wbm_burst_last_r <= 1'b0;
    end
    else if (wbm_cyc_o & (wbm_err_i | wbm_ack_i)) begin
      wbm_err_r        <= wbm_err_i;
      wbm_ack_r        <= wbm_ack_i;
      wbm_burst_last_r <= (burst_proc & burst_done_r[0]);
    end
    else begin
      wbm_err_r        <= 1'b0;
      wbm_ack_r        <= 1'b0;
      wbm_burst_last_r <= 1'b0;
    end
  end // @wb-clock
  // ---
  always @(posedge wb_clk) begin
    wbm_dat_r <= wbm_dat_i;
  end // @wb-clock

  // --- signaling to CPU ---
  reg   wbm2cpu_toggle_r;
  // ---
  always @(posedge wb_clk) begin
    if (wb_rst)
      wbm2cpu_toggle_r <= 1'b0;
    else if (wbm_cyc_o & (wbm_err_i | wbm_ack_i))
      wbm2cpu_toggle_r <= ~wbm2cpu_toggle_r;
  end // @wb-clock


  //
  // Pseudo CDC disclaimer:
  // As positive edges of wb-clock and cpu-clock assumed be aligned,
  // we use simplest clock domain pseudo-synchronizers.
  //
  reg   wbm2cpu_rdy_r1;
  wire  wbm2cpu_rdy_pulse = wbm2cpu_rdy_r1 ^ wbm2cpu_toggle_r; // from toggle to posedge of CPU clock
  // ---
  always @(posedge cpu_clk) begin
    if (cpu_rst)
      wbm2cpu_rdy_r1 <= 1'b0;
    else
      wbm2cpu_rdy_r1 <= wbm2cpu_toggle_r;
  end // @cpu-clock

  // To CPU ACK/ERR/BurstLast (with reset control)
  always @(posedge cpu_clk) begin
    if (cpu_rst) begin
      cpu_err_o        <= 1'b0;
      cpu_ack_o        <= 1'b0;
      cpu_burst_last_o <= 1'b0;
    end
    else if (wbm2cpu_rdy_pulse) begin
      cpu_err_o        <= wbm_err_r;
      cpu_ack_o        <= wbm_ack_r;
      cpu_burst_last_o <= wbm_burst_last_r;
    end
    else begin // 1-clock
      cpu_err_o        <= 1'b0;
      cpu_ack_o        <= 1'b0;
      cpu_burst_last_o <= 1'b0;
    end
  end // at cpu-clock

  // To CPU DATA
  always @(posedge cpu_clk) begin
    cpu_dat_o <= wbm_dat_r;
  end // at cpu-clock


  //----------------------------------------------------------//
  // Atomic (l.lwa/l.swa) and DCACHE snoop-invalidate support //
  //----------------------------------------------------------//

  // snoop hit for l.swa in multicore machine
  generate
  /* verilator lint_off WIDTH */
  if ((DRIVER_TYPE == "D_CACHE") && (OPTION_DCACHE_SNOOP != "NONE")) begin: dbus_multi_core
  /* verilator lint_on WIDTH */

    //
    // Latched attributes of snoop event.
    //
    wire       snoop_en_f = snoop_en_i & (~wbm_ack_i) & (~wbm_err_i);  // DBUS multi core bridge
    reg        snoop_en_r;
    reg [31:0] snoop_adr_r;
    //
    // We don't care about self-snoop because:
    //  (a) for atomic reservation flag it operates in the same way
    //      as 'reset by l.swa completion' logic
    //  (b) DBUS's ACK has got priority in DBUS controller
    //
    always @(posedge wb_clk) begin
      if (wb_rst)
        snoop_en_r <= 1'b0; // at reset
      else if (snoop_en_f)  // rise local register, DBUS multi core bridge
        snoop_en_r <= 1'b1;
      else
        snoop_en_r <= (~cpu_snoop_inv_ack) & snoop_en_r;
    end
    //
    // latch snooped address
    //
    always @(posedge wb_clk) begin
      snoop_adr_r <= snoop_adr_i;
    end
    //
    // local snoop data for atomic reservation check
    //
    assign snoop_en_l  = snoop_en_r;        // DBUS multi core bridge
    assign snoop_adr_l = snoop_adr_r[31:2]; // DBUS multi core bridge


    //
    // Snoop Event -> DCACHE
    //
    // Pseudo CDC disclaimer:
    // As positive edges of wb-clock and cpu-clock assumed be aligned,
    // we use simplest clock domain pseudo-synchronizers.
    //
    // --- toggle ---
    reg  snoop_en_toggle_r;
    // ---
    always @(posedge wb_clk) begin
      if (wb_rst)
        snoop_en_toggle_r <= 1'b0;
      else if (snoop_en_f)
        snoop_en_toggle_r <= ~snoop_en_toggle_r;
    end
    // --- to CPU pulse ---
    reg  wbm2cpu_snoop_en_r;
    wire wbm2cpu_snoop_en_pulse = wbm2cpu_snoop_en_r ^ snoop_en_toggle_r;
    // ---
    always @(posedge cpu_clk) begin
      if (cpu_rst)
        wbm2cpu_snoop_en_r <= 1'b0;
      else
        wbm2cpu_snoop_en_r <= snoop_en_toggle_r;
    end
    // --- CPU visibility ---
    reg         cpu_snoop_en_r;
    reg  [31:0] cpu_snoop_adr_r;
    // ---
    always @(posedge cpu_clk) begin
      if (cpu_rst)
        cpu_snoop_en_r <= 1'b0;
      else
        cpu_snoop_en_r <= wbm2cpu_snoop_en_pulse;
    end
    // ---
    always @(posedge cpu_clk) begin
      cpu_snoop_adr_r <= snoop_adr_r;
    end
    // --- ports assignement ---
    assign cpu_snoop_adr_o = cpu_snoop_adr_r; // DBUS multi core bridge
    assign cpu_snoop_en_o  = cpu_snoop_en_r;  // DBUS multi core bridge


    //
    // DCACHE Snoop ACK ->  DBUS Bridge
    // We implement the ACK here without routing in DCACHE because
    // it's timing guaranties that the chain:
    //    DCAHCE Snoop ACK ->
    //      Restoring DBUS request ->
    //        DBUS Brige ACK ->
    //          Provide DBUS Brige ACK to DCACHE
    // completes even later than DCACHE Snoop invalidation even for
    // fastest "DBUS Brige ACK" and ("CPU clock" == "Wishbone clock")
    //
    // Pseudo CDC disclaimer:
    // As positive edges of wb-clock and cpu-clock assumed be aligned,
    // we use simplest clock domain pseudo-synchronizers.
    //
    // --- toggle ---
    reg  dc_snoop_inv_ack_toggle_r;
    // ---
    always @(posedge cpu_clk) begin
      if (cpu_rst)
        dc_snoop_inv_ack_toggle_r <= 1'b0;
      else if (cpu_snoop_en_o)              // Toggle DCAHCE Snoop ACK
        dc_snoop_inv_ack_toggle_r <= ~dc_snoop_inv_ack_toggle_r;
    end
    // --- DCAHCE Snoop ACK pulse (eq. to others CPU side signals) ---
    reg    cpu_snoop_inv_ack_r1, cpu_snoop_inv_ack_r2;
    assign cpu_snoop_inv_ack = cpu_snoop_inv_ack_r1 ^ cpu_snoop_inv_ack_r2;
    // ---
    always @(posedge wb_clk) begin
      if (wb_rst) begin
        cpu_snoop_inv_ack_r2 <= 1'b0;
        cpu_snoop_inv_ack_r1 <= 1'b0;
      end
      else begin
        cpu_snoop_inv_ack_r2 <= cpu_snoop_inv_ack_r1;
        cpu_snoop_inv_ack_r1 <= dc_snoop_inv_ack_toggle_r;
      end
    end

  end
  else begin: dbus_single_core

    assign snoop_en_l  =  1'b0; // IBUS bridge or Single Core machine
    assign snoop_adr_l = 30'd0; // IBUS bridge or Single Core machine

    assign cpu_snoop_adr_o = 32'd0; // IBUS bridge or Single Core machine
    assign cpu_snoop_en_o  =  1'b0; // IBUS bridge or Single Core machine

    assign cpu_snoop_inv_ack = 1'b1; // IBUS bridge or Single Core machine

  end
  endgenerate

  // Atomic reservation flag and address are placed in
  // Wishbown clock domain to exclude possible misalign
  // during crossing propagations:
  //  (a) snoop hits from Wishbone to CPU
  //  (b) l.swa from CPU to Wishbone
  // ---
  generate
  /* verilator lint_off WIDTH */
  if (DRIVER_TYPE == "D_CACHE") begin: dbus_with_atomics
  /* verilator lint_on WIDTH */

    // Clock domain crossing fo pipeline-flush to
    // clean up atomic reservation flag at context switch.
    //
    // Pseudo CDC disclaimer:
    // As positive edges of wb-clock and cpu-clock assumed be aligned,
    // we use simplest clock domain pseudo-synchronizers.
    //
    reg  pipeline_flush_toggle_r;
    reg  pipeline_flush_state_r;  // to prevent multiple toggling for case of multi-clock pipeline-flush
    // ---
    always @(posedge cpu_clk) begin
      if (cpu_rst) begin
        pipeline_flush_toggle_r <= 1'b0;
        pipeline_flush_state_r  <= 1'b0;
      end
      else if (pipeline_flush_state_r) begin
        pipeline_flush_toggle_r <= pipeline_flush_toggle_r;
        pipeline_flush_state_r  <= pipeline_flush_i;
      end
      else if (pipeline_flush_i) begin
        pipeline_flush_toggle_r <= ~pipeline_flush_toggle_r;
        pipeline_flush_state_r  <= 1'b1;
      end
    end // @cpu-clock
    // ---
    reg  pipeline_flush_r1;
    wire pipeline_flush_pulse = pipeline_flush_toggle_r ^ pipeline_flush_r1; // from toggle to posedge of Wishbone clock
    // ---
    always @(posedge wb_clk) begin
      if (wb_rst)
        pipeline_flush_r1 <= 1'b0;
      else
        pipeline_flush_r1 <= pipeline_flush_toggle_r;
    end // @cpu-clock
    // ---
    // no re-fill for l.swa (see LSU and DCACHE),
    // so needn't taking into accaunt bursting here
    reg  flush_r;
    // ---
    always @(posedge wb_clk) begin
      if (wb_rst)
        flush_r <= 1'b0;
      else if (wbm_err_r | wbm_ack_r)
        flush_r <= 1'b0;
      else if (pipeline_flush_pulse)
        flush_r <= wbm_cyc_o;
    end // @cpu-clock


    // Atomic related declarations
    reg         atomic_flg_r; // reservation flag
    reg  [29:0] atomic_adr_r; // linked address [31:2] of phys. address


    // store linked address from cache
    always @(posedge wb_clk) begin
      if (wb_rst)
        atomic_adr_r <= 30'd0;
      else if (lwa_cmd & wbm_ack_r)       // save linked address
        atomic_adr_r <= cpu_adr_r1[31:2];
    end


    // atomic reserve flag
    wire deassert_atomic_flg =
      pipeline_flush_pulse | flush_r | // deassert atomic flag by context switch
      (stna_cmd   & atomic_flg_r & (atomic_adr_r == cpu_adr_r1[31:2])) | // deassert atomic flag by store to the same location
      (swa_cmd    & atomic_flg_r & (atomic_adr_r != cpu_adr_r1[31:2])) | // deassert atomic flag by l.swa to another location
      (snoop_en_l & atomic_flg_r & (atomic_adr_r == snoop_adr_l))      | // deassert atomic flag by snoop hit
      (swa_cmd & (wbm_err_r | wbm_ack_r)); // deassert atomic flag by l.swa completion
    // ---
    always @(posedge wb_clk) begin
      if (wb_rst)
        atomic_flg_r <= 1'b0;
      else if (deassert_atomic_flg)
        atomic_flg_r <= 1'b0;
      else if (lwa_cmd & wbm_ack_r)    // update linked flag
        atomic_flg_r <= ~atomic_flg_r; // assert by "1-st" l.lwa, deassert by another l.lwa
    end
    // ---
    assign atomic_flg = atomic_flg_r; // DBUS bridge


    // transfer atomic reserve flag to CPU
    reg to_cpu_atomic_flg_r1;
    // ---
    always @(posedge cpu_clk) begin
      if (wbm2cpu_rdy_pulse)
        to_cpu_atomic_flg_r1 <= atomic_flg_r;
    end // at cpu-clock

    // output assignement
    assign cpu_atomic_flg_o = to_cpu_atomic_flg_r1; // DBUS bridge

  end // atomic_support
  else begin : ibus_without_atomics

    // CPU request clarifications
    assign lwa_cmd          =  1'b0; // IBUS bridge
    assign stna_cmd         =  1'b0; // IBUS bridge
    assign swa_cmd          =  1'b0; // IBUS bridge

    // atomic reservation flag
    assign atomic_flg       =  1'b0; // IBUS bridge
    // "to CPU" output
    assign cpu_atomic_flg_o =  1'b0; // IBUS bridge

  end
  endgenerate

endmodule // mor1kx_bus_if_wb32_marocchino
