//////////////////////////////////////////////////////////////////////
//                                                                  //
//  mor1kx_rf_marocchino                                            //
//                                                                  //
//  Description:                                                    //
//    Register file for MAROCCHINO pipeline                         //
//    Derived from mor1kx_rf_cappuccino                             //
//                                                                  //
//////////////////////////////////////////////////////////////////////
//                                                                  //
//   Copyright (C) 2012 Julius Baxter                               //
//                      juliusbaxter@gmail.com                      //
//                                                                  //
//   Copyright (C) 2012-2014 Stefan Kristiansson                    //
//                           stefan.kristiansson@saunalahti.fi      //
//                                                                  //
//   Copyright (C) 2015-2018 Andrey Bacherov                        //
//                           avbacherov@opencores.org               //
//                                                                  //
//      This Source Code Form is subject to the terms of the        //
//      Open Hardware Description License, v. 1.0. If a copy        //
//      of the OHDL was not distributed with this file, You         //
//      can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt     //
//                                                                  //
//////////////////////////////////////////////////////////////////////

`include "mor1kx-defines.v"

/****************************************************/
/* Regiter File with Shadow GPRs and SPR BUS access */
/****************************************************/

module mor1kx_rf_marocchino
#(
  parameter OPTION_RF_CLEAR_ON_INIT  =  0,
  parameter OPTION_RF_ADDR_WIDTH     =  5,
  parameter NUM_GPRS                 = 32, // (1 << OPTION_RF_ADDR_WIDTH)
  parameter OPTION_OPERAND_WIDTH     = 32,
  parameter FEATURE_DEBUGUNIT        = "NONE",
  parameter OPTION_RF_NUM_SHADOW_GPR =  0       // for multicore mostly
)
(
  input                                 cpu_clk,
  input                                 cpu_rst,

  // pipeline control signals
  input                                 pipeline_flush_i,
  input                                 padv_dcod_i,

  // SPR bus
  input                          [15:0] spr_bus_addr_i,
  input                                 spr_bus_stb_i,
  input                                 spr_bus_we_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_i,
  output                                spr_bus_ack_gpr0_o,
  output     [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_gpr0_o,
  output                                spr_bus_ack_gprS_o,
  output     [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_gprS_o,

  // from FETCH
  input      [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfa1_adr_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfb1_adr_i,
  // for FPU64
  input      [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfa2_adr_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfb2_adr_i,

  // from DECODE
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_immediate_i,
  input                                 dcod_immediate_sel_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa1_adr_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb1_adr_i,
  // for FPU64
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa2_adr_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb2_adr_i,

  // from Write-Back
  input                                 wrbk_rfd1_we_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] wrbk_rfd1_adr_i,
  input      [OPTION_OPERAND_WIDTH-1:0] wrbk_result1_i,
  // for FPU64
  input                                 wrbk_rfd2_we_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] wrbk_rfd2_adr_i,
  input      [OPTION_OPERAND_WIDTH-1:0] wrbk_result2_i,

  // outputs (combinatorial)
  output reg [OPTION_OPERAND_WIDTH-1:0] dcod_rfa1_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] dcod_rfb1_o,
  // for FPU64
  output     [OPTION_OPERAND_WIDTH-1:0] dcod_rfa2_o,
  output     [OPTION_OPERAND_WIDTH-1:0] dcod_rfb2_o,

  // we use adder in EXECUTE to compute return address (pc+8) for l.jl/l.jalr
  input                                 dcod_op_jal_i,
  input      [OPTION_OPERAND_WIDTH-1:0] pc_decode_i,

  // Special case for l.jr/l.jalr
  output     [OPTION_OPERAND_WIDTH-1:0] dcod_rfb1_jr_o
);

  // short names
  localparam RF_AW = OPTION_RF_ADDR_WIDTH;
  localparam RF_DW = OPTION_OPERAND_WIDTH;

  // Declarations of RAM blocks output
  wire [RF_DW-1:0] ram_rfa1_out;
  wire [RF_DW-1:0] ram_rfa2_out;
  wire [RF_DW-1:0] ram_rfb1_out;
  wire [RF_DW-1:0] ram_rfb2_out;


  //--------------------------------------//
  // Common part of SPR BUS               //
  //--------------------------------------//
  // Registering SPR BUS incoming signals //
  // as they are common for GPR Group #0  //
  // and GPR Shadow.                      //
  //--------------------------------------//

  //  we don't expect R/W-collisions for SPRbus vs Write-Back cycles since
  //    SPRbus access start 1-clock later than Write-Back
  //    thanks to MT(F)SPR processing logic (see OMAN)

  // SPR BUS strobe registering
  reg spr_bus_stb_r;
  // ---
  always @(posedge cpu_clk) begin
    if (cpu_rst)
      spr_bus_stb_r <= 1'b0;
    else if (spr_bus_ack_gpr0_o | spr_bus_ack_gprS_o)
      spr_bus_stb_r <= 1'b0;
    else
      spr_bus_stb_r <= spr_bus_stb_i;
  end // at clock

  // SPR BUS address registering
  reg [15:0] spr_bus_addr_r;
  // ---
  always @(posedge cpu_clk) begin
    spr_bus_addr_r <= spr_bus_addr_i;
  end

  // Registering SPR BUS "write strobe" and "data for write".
  wire               spr_bus_we_l;
  wire [(RF_DW-1):0] spr_bus_dat_l;

  generate
  /* verilator lint_off WIDTH */
  if ((FEATURE_DEBUGUNIT != "NONE") || (OPTION_RF_NUM_SHADOW_GPR > 0)) begin : spr_aux_enabled
  /* verilator lint_on WIDTH */

    // Registering SPR BUS "write strobe" and "data for write".
    reg               spr_bus_we_r; // DBGU or SHADOW
    reg [(RF_DW-1):0] spr_bus_dat_r; // DBGU or SHADOW
    // ---
    assign spr_bus_we_l  = spr_bus_we_r; // DBGU or SHADOW
    assign spr_bus_dat_l = spr_bus_dat_r; // DBGU or SHADOW
    // ---
    always @(posedge cpu_clk) begin
      spr_bus_we_r  <= spr_bus_we_i; // DBGU or SHADOW
      spr_bus_dat_r <= spr_bus_dat_i; // DBGU or SHADOW
    end // at clock

  end
  else begin : spr_aux_disabled

    assign spr_bus_we_l  = 1'b0;          // No DBGU and No SHADOW
    assign spr_bus_dat_l = {RF_DW{1'b0}}; // No DBGU and No SHADOW

  end
  endgenerate


  //--------------//
  // GPR [S]hadow //
  //--------------//

  `include "mor1kx_utils.vh"

  function integer calc_shadow_addr_width;
    input integer rf_addr_width;
    input integer rf_num_shadow_gpr;
    calc_shadow_addr_width  = rf_addr_width +
                              ((rf_num_shadow_gpr == 1) ? 1 :
                               `clog2(rf_num_shadow_gpr));
  endfunction

  localparam SHADOW_AW = calc_shadow_addr_width(OPTION_RF_ADDR_WIDTH,
                                                OPTION_RF_NUM_SHADOW_GPR);

  // GPR[S]hadow chip select
  // low bits of SPR-address are used for addressing GPR[S]hadow
  wire spr_gprS_cs = spr_bus_stb_r &                  // GPR[S]hadow access
                     (spr_bus_addr_r[15:9] == 7'd2) & // GPR[S]hadow access, same to OR1K_SPR_GPR0_ADDR
                     (spr_bus_addr_r[ 8:5] != 4'd0);  // GPR[S]hadow access

  // We declare states or SPR BUS FSM here because some
  // of EDA tools deprecate local parameters declaration
  // inside of generate blocks.

  localparam  [4:0] SPR_GPRS_WAITING = 5'b00001,
                    SPR_GPRS_WE_STRB = 5'b00010,
                    SPR_GPRS_RE_STRB = 5'b00100,
                    SPR_GPRS_READ_MX = 5'b01000,
                    SPR_GPRS_ACK     = 5'b10000;

  generate
  /* verilator lint_off WIDTH */
  if (OPTION_RF_NUM_SHADOW_GPR > 0) begin : shadow_enabled
  /* verilator lint_on WIDTH */

    // SPR BUS FSM states
    reg         [4:0] spr_gprS_state;

    // Particular states
    //wire              spr_gprS_waiting_state = spr_gprS_state[0];
    wire              spr_gprS_we_strb_state = spr_gprS_state[1];
    wire              spr_gprS_re_strb_state = spr_gprS_state[2];
    wire              spr_gprS_read_mx_state = spr_gprS_state[3];
    assign            spr_bus_ack_gprS_o     = spr_gprS_state[4];

    // Read data
    reg [(RF_DW-1):0] spr_bus_dat_gprS_r;


    // SPR BUS FSM
    always @(posedge cpu_clk) begin
      if (cpu_rst) begin
        spr_gprS_state <= SPR_GPRS_WAITING;
      end
      else begin
        // synthesis parallel_case
        case (spr_gprS_state)
          // waiting Shadow GPRs access
          SPR_GPRS_WAITING: begin
            if (spr_gprS_cs) begin
              spr_gprS_state <= spr_bus_we_l ? SPR_GPRS_WE_STRB : SPR_GPRS_RE_STRB;
            end
          end

          // write strobe
          SPR_GPRS_WE_STRB: begin
            spr_gprS_state <= SPR_GPRS_ACK;
          end

          // read strobe
          SPR_GPRS_RE_STRB: begin
            spr_gprS_state <= SPR_GPRS_READ_MX;
          end

          // latch data for read
          SPR_GPRS_READ_MX: begin
            spr_gprS_state <= SPR_GPRS_ACK;
          end

          // done
          SPR_GPRS_ACK: begin
            spr_gprS_state <= SPR_GPRS_WAITING;
          end

          default;
        endcase
      end
    end // @ clock


    // registered output data: valid for 1-clock only with rised ACK
    wire [(RF_DW-1):0] rfS_dout;
    // ---
    always @(posedge cpu_clk) begin
      spr_bus_dat_gprS_r <= {RF_DW{spr_gprS_read_mx_state}} & // SPR GPR[S]hadow read latch
                            rfS_dout; // SPR GPR[S]hadow read latch
    end
    // ---
    assign spr_bus_dat_gprS_o = spr_bus_dat_gprS_r; // SHADOW enabled


    // Shadow RAM instance
    mor1kx_spram_en_w1st
    #(
      .ADDR_WIDTH     (SHADOW_AW),
      .DATA_WIDTH     (RF_DW),
      .CLEAR_ON_INIT  (OPTION_RF_CLEAR_ON_INIT)
    )
    rfShadow
    (
      // clock
      .clk    (cpu_clk),
      // port
      .en     (spr_gprS_we_strb_state | spr_gprS_re_strb_state),
      .we     (spr_gprS_we_strb_state),
      .addr   (spr_bus_addr_r[(SHADOW_AW-1):0]),
      .din    (spr_bus_dat_l),
      .dout   (rfS_dout)
    );

  end
  else begin: shadow_disabled

    // make ACK
    reg    spr_bus_ack_gprS_r;
    assign spr_bus_ack_gprS_o = spr_bus_ack_gprS_r; // SHADOW disabled
    // ---
    always @(posedge cpu_clk) begin
      if (cpu_rst)
        spr_bus_ack_gprS_r <= 1'b0;
      else if (spr_bus_ack_gprS_r)
        spr_bus_ack_gprS_r <= 1'b0;
      else if (spr_gprS_cs)
        spr_bus_ack_gprS_r <= 1'b1;
    end

    // SPR data output
    assign spr_bus_dat_gprS_o = {RF_DW{1'b0}}; // SHADOW disabled

  end
  endgenerate


  //----------------------------------//
  // SPR BUS for Group #0 GPRs access //
  //----------------------------------//

  // Group #0 GPRs chip select
  wire spr_gpr0_cs = spr_bus_stb_r &                  // Group #0 GPRs access
                     (spr_bus_addr_r[15:9] == 7'd2) & // Group #0 GPRs access, see OR1K_SPR_GPR0_ADDR
                     (spr_bus_addr_r[ 8:5] == 4'd0);  // Group #0 GPRs access

  // Group #0 GPRs controls
  wire                spr_gpr0_re;
  wire                spr_gpr0_we;
  wire    [RF_AW-1:0] spr_gpr0_addr = spr_bus_addr_r[RF_AW-1:0];
  wire    [RF_DW-1:0] spr_gpr0_data;

  // We declare states or SPR BUS FSM here because some
  // of EDA tools deprecate local parameters declaration
  // inside of generate blocks.

  localparam  [4:0] SPR_GPR0_WAITING = 5'b00001,
                    SPR_GPR0_WE_STRB = 5'b00010,
                    SPR_GPR0_RE_STRB = 5'b00100,
                    SPR_GPR0_READ_MX = 5'b01000,
                    SPR_GPR0_ACK     = 5'b10000;

  generate
  /* verilator lint_off WIDTH */
  if (FEATURE_DEBUGUNIT != "NONE") begin : dbgu_enabled
  /* verilator lint_on WIDTH */

    // SPR BUS FSM states
    reg         [4:0] spr_gpr0_state;

    // Particular states
    assign            spr_gpr0_we            = spr_gpr0_state[1]; // DBGU enabled
    assign            spr_gpr0_re            = spr_gpr0_state[2]; // DBGU enabled
    wire              spr_gpr0_read_mx_state = spr_gpr0_state[3];
    assign            spr_bus_ack_gpr0_o     = spr_gpr0_state[4]; // DBGU enabled

    // Read data
    reg     [RF_DW-1:0] spr_bus_dat_gpr0_r;
    assign              spr_bus_dat_gpr0_o = spr_bus_dat_gpr0_r; // DBGU enabled

    // SPR BUS FSM
    always @(posedge cpu_clk) begin
      if (cpu_rst) begin
        spr_gpr0_state <= SPR_GPR0_WAITING;
      end
      else begin
        // synthesis parallel_case
        case (spr_gpr0_state)
          // waiting Group #0 GPRs access
          SPR_GPR0_WAITING: begin
            if (spr_gpr0_cs) begin
              spr_gpr0_state <= spr_bus_we_l ? SPR_GPR0_WE_STRB : SPR_GPR0_RE_STRB;
            end
          end

          // write strobe
          SPR_GPR0_WE_STRB: begin
            spr_gpr0_state <= SPR_GPR0_ACK;
          end

          // read strobe
          SPR_GPR0_RE_STRB: begin
            spr_gpr0_state <= SPR_GPR0_READ_MX;
          end

          // latch data for read
          SPR_GPR0_READ_MX: begin
            spr_gpr0_state <= SPR_GPR0_ACK;
          end

          // done
          SPR_GPR0_ACK: begin
            spr_gpr0_state <= SPR_GPR0_WAITING;
          end

          default;
        endcase
      end
    end // @ clock

    // registered output data: valid for 1-clock only with rised ACK
    always @(posedge cpu_clk) begin
      spr_bus_dat_gpr0_r <= spr_gpr0_data & {RF_DW{spr_gpr0_read_mx_state}};
    end

  end
  else begin : dbgu_disabled

    // Read/Write enables
    assign spr_gpr0_re = 1'b0; // DBGU disabled
    assign spr_gpr0_we = 1'b0; // DBGU disabled

    // SPR data output
    assign spr_bus_dat_gpr0_o = {RF_DW{1'b0}}; // DBGU disabled

    // make ACK
    reg    spr_bus_ack_gpr0_r;
    assign spr_bus_ack_gpr0_o = spr_bus_ack_gpr0_r; // DBGU disabled
    // ---
    always @(posedge cpu_clk) begin
      if (cpu_rst)
        spr_bus_ack_gpr0_r <= 1'b0;
      else if (spr_bus_ack_gpr0_r)
        spr_bus_ack_gpr0_r <= 1'b0;
      else if (spr_gpr0_cs)
        spr_bus_ack_gpr0_r <= 1'b1;
    end

  end
  endgenerate


  //-----------------------//
  // Forwarding Conditions //
  //-----------------------//

  // Note: actually we perdorm D2->Ax/Bx writting
  //       when DECODE, EXECUTE & WRITE-BACK are stalled.
  //       That means D2-related WriteBack-to-Fetch hazards
  //       are not possible. And D2-related WriteBack-to-Decode
  //       hazards are resolved through RAM-write (without
  //       multiplexing at DECODE's output).

  // WriteBack-to-Fetch
  //  # D1 <-> A1
  wire wrb2fth_d1a1_equ = (wrbk_rfd1_adr_i == fetch_rfa1_adr_i);
  wire wrb2fth_d1a1_fwd = wrbk_rfd1_we_i & wrb2fth_d1a1_equ;
  //  # D1 <-> A2
  wire wrb2fth_d1a2_equ = (wrbk_rfd1_adr_i == fetch_rfa2_adr_i);
  wire wrb2fth_d1a2_fwd = wrbk_rfd1_we_i & wrb2fth_d1a2_equ;
  //  # D1 <-> B1
  wire wrb2fth_d1b1_equ = (wrbk_rfd1_adr_i == fetch_rfb1_adr_i);
  wire wrb2fth_d1b1_fwd = wrbk_rfd1_we_i & wrb2fth_d1b1_equ;
  //  # D1 <-> B2
  wire wrb2fth_d1b2_equ = (wrbk_rfd1_adr_i == fetch_rfb2_adr_i);
  wire wrb2fth_d1b2_fwd = wrbk_rfd1_we_i & wrb2fth_d1b2_equ;

  // WriteBack-to-Decode
  //  # D1 <-> A1
  wire wrb2dec_d1a1_equ = (wrbk_rfd1_adr_i == dcod_rfa1_adr_i);
  wire wrb2dec_d1a1_fwd = wrbk_rfd1_we_i & wrb2dec_d1a1_equ;
  //  # D2 <-> A1
  wire wrb2dec_d2a1_equ = (wrbk_rfd2_adr_i == dcod_rfa1_adr_i);
  wire wrb2dec_d2a1_fwd = wrbk_rfd2_we_i & wrb2dec_d2a1_equ;
  //  # D1 <-> B1
  wire wrb2dec_d1b1_equ = (wrbk_rfd1_adr_i == dcod_rfb1_adr_i);
  wire wrb2dec_d1b1_fwd = wrbk_rfd1_we_i & wrb2dec_d1b1_equ;
  //  # D2 <-> B1
  wire wrb2dec_d2b1_equ = (wrbk_rfd2_adr_i == dcod_rfb1_adr_i);
  wire wrb2dec_d2b1_fwd = wrbk_rfd2_we_i & wrb2dec_d2b1_equ;
  //  # D1 <-> A2
  wire wrb2dec_d1a2_equ = (wrbk_rfd1_adr_i == dcod_rfa2_adr_i);
  wire wrb2dec_d1a2_fwd = wrbk_rfd1_we_i & wrb2dec_d1a2_equ;
  //  # D2 <-> A2
  wire wrb2dec_d2a2_equ = (wrbk_rfd2_adr_i == dcod_rfa2_adr_i);
  wire wrb2dec_d2a2_fwd = wrbk_rfd2_we_i & wrb2dec_d2a2_equ;
  //  # D1 <-> B2
  wire wrb2dec_d1b2_equ = (wrbk_rfd1_adr_i == dcod_rfb2_adr_i);
  wire wrb2dec_d1b2_fwd = wrbk_rfd1_we_i & wrb2dec_d1b2_equ;
  //  # D2 <-> B2
  wire wrb2dec_d2b2_equ = (wrbk_rfd2_adr_i == dcod_rfb2_adr_i);
  wire wrb2dec_d2b2_fwd = wrbk_rfd2_we_i & wrb2dec_d2b2_equ;


  //-------------------------//
  // Generic Inputs for RAMs //
  //-------------------------//

  wire [RF_DW-1:0] ram_xx_pa_data  = wrbk_rfd1_we_i ? wrbk_result1_i : wrbk_result2_i;

  wire             spr_gpr0_access = spr_gpr0_we | spr_gpr0_re;

  wire [RF_DW-1:0] ram_xx_pb_data  = spr_gpr0_access ? spr_bus_dat_l  : ram_xx_pa_data;
  wire [RF_AW-1:0] ram_xx_pb_addr  = spr_gpr0_access ? spr_gpr0_addr :
                                      (wrbk_rfd1_we_i ? wrbk_rfd1_adr_i : wrbk_rfd2_adr_i);


  //------------------//
  // RAM block for A1 //
  //------------------//

  // --- RAM-A1 port A controls ---
  wire wrb2dec_dxa1_pa_we = wrb2dec_d1a1_fwd | wrb2dec_d2a1_fwd;
  //  # enable
  wire ram_a1_pa_en = padv_dcod_i ? 1'b1 : (wrb2dec_dxa1_pa_we |
                                            spr_bus_ack_gpr0_o); // re-read after DU or l.mXspr access
  //  # do write
  wire ram_a1_pa_we = padv_dcod_i ? wrb2fth_d1a1_fwd : wrb2dec_dxa1_pa_we;
  //  # address
  wire [RF_AW-1:0] ram_a1_pa_addr = padv_dcod_i ? fetch_rfa1_adr_i : dcod_rfa1_adr_i;

  // --- RAM-A1 port B controls ---
  wire wrb2fth_d1a1_pb_we =  wrbk_rfd1_we_i & (~wrb2fth_d1a1_equ);
  wire wrb2dec_dxa1_pb_we = (wrbk_rfd1_we_i & (~wrb2dec_d1a1_equ)) |
                            (wrbk_rfd2_we_i & (~wrb2dec_d2a1_equ));
 //  # enable
  wire ram_a1_pb_en = padv_dcod_i ? wrb2fth_d1a1_pb_we :
                                   (wrb2dec_dxa1_pb_we | spr_gpr0_access);
  //  # do write
  wire ram_a1_pb_we = padv_dcod_i ? wrb2fth_d1a1_pb_we :
                                   (wrb2dec_dxa1_pb_we | spr_gpr0_we);

  // --- RAM-A1 instance ---
  mor1kx_dpram_en_w1st
  #(
    .ADDR_WIDTH     (RF_AW), // RAM-A1
    .DATA_WIDTH     (RF_DW), // RAM-A1
    .CLEAR_ON_INIT  (OPTION_RF_CLEAR_ON_INIT) // RAM-A1
  )
  u_ram_a1
  (
    // port "a"
    .clk_a    (cpu_clk), // RAM-A1
    .en_a     (ram_a1_pa_en), // RAM-A1
    .we_a     (ram_a1_pa_we & (~pipeline_flush_i)), // RAM-A1
    .addr_a   (ram_a1_pa_addr), // RAM-A1
    .din_a    (ram_xx_pa_data), // RAM-A1
    .dout_a   (ram_rfa1_out), // RAM-A1
    // port "b"
    .clk_b    (cpu_clk),
    .en_b     (ram_a1_pb_en), // RAM-A1
    .we_b     (ram_a1_pb_we & (~pipeline_flush_i)), // RAM-A1
    .addr_b   (ram_xx_pb_addr), // RAM-A1
    .din_b    (ram_xx_pb_data), // RAM-A1
    .dout_b   (spr_gpr0_data) // RAM-A1
  );


  //------------------//
  // RAM block for B1 //
  //------------------//

  // --- RAM-B1 port A controls ---
  wire wrb2dec_dxb1_pa_we = wrb2dec_d1b1_fwd | wrb2dec_d2b1_fwd;
  //  # enable
  wire ram_b1_pa_en = padv_dcod_i ? 1'b1 : (wrb2dec_dxb1_pa_we |
                                            spr_bus_ack_gpr0_o); // re-read after DU or l.mXspr access
  //  # do write
  wire ram_b1_pa_we = padv_dcod_i ? wrb2fth_d1b1_fwd : wrb2dec_dxb1_pa_we;
  //  # address
  wire [RF_AW-1:0] ram_b1_pa_addr = padv_dcod_i ? fetch_rfb1_adr_i : dcod_rfb1_adr_i;

  // --- RAM-B1 port B controls ---
  wire wrb2fth_d1b1_pb_we =  wrbk_rfd1_we_i & (~wrb2fth_d1b1_equ);
  wire wrb2dec_dxb1_pb_we = (wrbk_rfd1_we_i & (~wrb2dec_d1b1_equ)) |
                            (wrbk_rfd2_we_i & (~wrb2dec_d2b1_equ));
  //  # enable
  wire ram_b1_pb_en = padv_dcod_i ? wrb2fth_d1b1_pb_we :
                                   (wrb2dec_dxb1_pb_we | spr_gpr0_we);
  //  # do write
  wire ram_b1_pb_we = ram_b1_pb_en;

  // --- RAM-B1 instance ---
  mor1kx_dpram_en_w1st
  #(
    .ADDR_WIDTH     (RF_AW), // RAM-B1
    .DATA_WIDTH     (RF_DW), // RAM-B1
    .CLEAR_ON_INIT  (OPTION_RF_CLEAR_ON_INIT) // RAM-B1
  )
  u_ram_b1
  (
    // port "a"
    .clk_a    (cpu_clk), // RAM-B1
    .en_a     (ram_b1_pa_en), // RAM-B1
    .we_a     (ram_b1_pa_we & (~pipeline_flush_i)), // RAM-B1
    .addr_a   (ram_b1_pa_addr), // RAM-B1
    .din_a    (ram_xx_pa_data), // RAM-B1
    .dout_a   (ram_rfb1_out), // RAM-B1
    // port "b"
    .clk_b    (cpu_clk),
    .en_b     (ram_b1_pb_en), // RAM-B1
    .we_b     (ram_b1_pb_we & (~pipeline_flush_i)), // RAM-B1
    .addr_b   (ram_xx_pb_addr), // RAM-B1
    .din_b    (ram_xx_pb_data) // RAM-B1
    //.dout_b   () // RAM-B1
  );


  //------------------//
  // RAM block for A2 //
  //------------------//

  // --- RAM-A2 port A controls ---
  wire wrb2dec_dxa2_pa_we = wrb2dec_d1a2_fwd | wrb2dec_d2a2_fwd;
  //  # enable
  wire ram_a2_pa_en = padv_dcod_i ? 1'b1 : (wrb2dec_dxa2_pa_we |
                                            spr_bus_ack_gpr0_o); // re-read after DU or l.mXspr access
  //  # do write
  wire ram_a2_pa_we = padv_dcod_i ? wrb2fth_d1a2_fwd : wrb2dec_dxa2_pa_we;
  //  # address
  wire [RF_AW-1:0] ram_a2_pa_addr = padv_dcod_i ? fetch_rfa2_adr_i : dcod_rfa2_adr_i;

  // --- RAM-A2 port B controls ---
  wire wrb2fth_d1a2_pb_we =  wrbk_rfd1_we_i & (~wrb2fth_d1a2_equ);
  wire wrb2dec_dxa2_pb_we = (wrbk_rfd1_we_i & (~wrb2dec_d1a2_equ)) |
                            (wrbk_rfd2_we_i & (~wrb2dec_d2a2_equ));
  //  # enable
  wire ram_a2_pb_en = padv_dcod_i ? wrb2fth_d1a2_pb_we :
                                   (wrb2dec_dxa2_pb_we | spr_gpr0_we);
  //  # do write
  wire ram_a2_pb_we = ram_a2_pb_en;

  // --- RAM-A2 instance ---
  mor1kx_dpram_en_w1st
  #(
    .ADDR_WIDTH     (RF_AW), // RAM-A2
    .DATA_WIDTH     (RF_DW), // RAM-A2
    .CLEAR_ON_INIT  (OPTION_RF_CLEAR_ON_INIT) // RAM-A2
  )
  u_ram_a2
  (
    // port "a"
    .clk_a    (cpu_clk), // RAM-A2
    .en_a     (ram_a2_pa_en), // RAM-A2
    .we_a     (ram_a2_pa_we & (~pipeline_flush_i)), // RAM-A2
    .addr_a   (ram_a2_pa_addr), // RAM-A2
    .din_a    (ram_xx_pa_data), // RAM-A2
    .dout_a   (ram_rfa2_out), // RAM-A2
    // port "b"
    .clk_b    (cpu_clk),
    .en_b     (ram_a2_pb_en), // RAM-A2
    .we_b     (ram_a2_pb_we & (~pipeline_flush_i)), // RAM-A2
    .addr_b   (ram_xx_pb_addr), // RAM-A2
    .din_b    (ram_xx_pb_data) // RAM-A2
    //.dout_b   () // RAM-A2
  );


  //------------------//
  // RAM block for B2 //
  //------------------//

  // --- RAM-B2 port A controls ---
  wire wrb2dec_dxb2_pa_we = wrb2dec_d1b2_fwd | wrb2dec_d2b2_fwd;
  //  # enable
  wire ram_b2_pa_en = padv_dcod_i ? 1'b1 : (wrb2dec_dxb2_pa_we |
                                            spr_bus_ack_gpr0_o); // re-read after DU or l.mXspr access
  //  # do write
  wire ram_b2_pa_we = padv_dcod_i ? wrb2fth_d1b2_fwd : wrb2dec_dxb2_pa_we;
  //  # address
  wire [RF_AW-1:0] ram_b2_pa_addr = padv_dcod_i ? fetch_rfb2_adr_i : dcod_rfb2_adr_i;

  // --- RAM-B2 port B controls ---
  wire wrb2fth_d1b2_pb_we =  wrbk_rfd1_we_i & (~wrb2fth_d1b2_equ);
  wire wrb2dec_dxb2_pb_we = (wrbk_rfd1_we_i & (~wrb2dec_d1b2_equ)) |
                            (wrbk_rfd2_we_i & (~wrb2dec_d2b2_equ));
  //  # enable
  wire ram_b2_pb_en = padv_dcod_i ? wrb2fth_d1b2_pb_we :
                                   (wrb2dec_dxb2_pb_we | spr_gpr0_we);
  //  # do write
  wire ram_b2_pb_we = ram_b2_pb_en;

  // --- RAM-B2 instance ---
  mor1kx_dpram_en_w1st
  #(
    .ADDR_WIDTH     (RF_AW), // RAM-B2
    .DATA_WIDTH     (RF_DW), // RAM-B2
    .CLEAR_ON_INIT  (OPTION_RF_CLEAR_ON_INIT) // RAM-B2
  )
  u_ram_b2
  (
    // port "a"
    .clk_a    (cpu_clk), // RAM-B2
    .en_a     (ram_b2_pa_en), // RAM-B2
    .we_a     (ram_b2_pa_we & (~pipeline_flush_i)), // RAM-B2
    .addr_a   (ram_b2_pa_addr), // RAM-B2
    .din_a    (ram_xx_pa_data), // RAM-B2
    .dout_a   (ram_rfb2_out), // RAM-B2
    // port "b"
    .clk_b    (cpu_clk),
    .en_b     (ram_b2_pb_en), // RAM-B2
    .we_b     (ram_b2_pb_we & (~pipeline_flush_i)), // RAM-B2
    .addr_b   (ram_xx_pb_addr), // RAM-B2
    .din_b    (ram_xx_pb_data) // RAM-B2
    //.dout_b   () // RAM-B2
  );


  //-----------------------//
  // DECODE stage (dcod_*) //
  //-----------------------//

  // Forwarding mux for RFA1-output
  always @(dcod_op_jal_i    or pc_decode_i    or
           wrb2dec_d1a1_fwd or wrbk_result1_i or
           ram_rfa1_out) begin
    // synthesis parallel_case
    casez ({dcod_op_jal_i, wrb2dec_d1a1_fwd})
      2'b1?:   dcod_rfa1_o = pc_decode_i;
      2'b01:   dcod_rfa1_o = wrbk_result1_i;
      default: dcod_rfa1_o = ram_rfa1_out;
    endcase
  end

  // Forwarding mux for RFB1-output
  always @(dcod_op_jal_i        or
           dcod_immediate_sel_i or dcod_immediate_i or
           wrb2dec_d1b1_fwd     or wrbk_result1_i   or
           ram_rfb1_out) begin
    // synthesis parallel_case
    casez ({dcod_op_jal_i, dcod_immediate_sel_i, wrb2dec_d1b1_fwd})
      3'b1??:  dcod_rfb1_o = 4'd8; // (FEATURE_DELAY_SLOT == "ENABLED")
      3'b01?:  dcod_rfb1_o = dcod_immediate_i;
      3'b001:  dcod_rfb1_o = wrbk_result1_i;
      default: dcod_rfb1_o = ram_rfb1_out;
    endcase
  end

  // A2/B2-outputs
  assign dcod_rfa2_o = wrb2dec_d1a2_fwd ? wrbk_result1_i : ram_rfa2_out;
  assign dcod_rfb2_o = wrb2dec_d1b2_fwd ? wrbk_result1_i : ram_rfb2_out;


  // Special case for l.jr/l.jalr
  //   (a) By default these instructions require B1 operand,
  //       so we implemented simlified path here
  //   (b) The output is used next clock to DECODE to form
  //       registered l.jr/l.jalr command
  //   (c) IFETCH generates bubbles till B1 completion
  assign dcod_rfb1_jr_o = ram_rfb1_out;

endmodule // mor1kx_rf_marocchino
