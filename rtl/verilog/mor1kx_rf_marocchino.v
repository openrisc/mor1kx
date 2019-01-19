//////////////////////////////////////////////////////////////////////
//                                                                  //
//  mor1kx_rf_marocchino                                            //
//                                                                  //
//  Description:                                                    //
//    Register file for MAROCCHINO pipeline                         //
//    Handles reading the register file rams and register bypassing //
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

/*****************************************/
/* Single GPR (Flip-Flop implementation) */
/*****************************************/

module single_gpr
#(
  parameter OPTION_OPERAND_WIDTH     = 32
)
(
  // clock
  input                             cpu_clk,

  // write back D1
  input                             wrbk_rfd1_we1h_i,
  input  [OPTION_OPERAND_WIDTH-1:0] wrbk_result1_i,
  // write back D2 for FPU64
  input                             wrbk_rfd2_we1h_i,
  input  [OPTION_OPERAND_WIDTH-1:0] wrbk_result2_i,
  // write by SPR BUS access
  input                             spr_gpr0_we_i,
  input  [OPTION_OPERAND_WIDTH-1:0] spr_gpr0_wdata_i,

  // content
  output [OPTION_OPERAND_WIDTH-1:0] gpr_o
);

  reg [OPTION_OPERAND_WIDTH-1:0] gpr_r;

  assign gpr_o = gpr_r;

  always @(posedge cpu_clk) begin
    gpr_r <= spr_gpr0_we_i ? spr_gpr0_wdata_i :
              (wrbk_rfd1_we1h_i ? wrbk_result1_i :
               (wrbk_rfd2_we1h_i ? wrbk_result2_i :
                                    gpr_r));
  end // at cpu clock

endmodule // single_gpr



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
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa2_adr_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb2_adr_i,

  // from Write-Back
  input                  [NUM_GPRS-1:0] wrbk_rfd1_we1h_i,
  input                                 wrbk_rfd1_we_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] wrbk_rfd1_adr_i,
  input      [OPTION_OPERAND_WIDTH-1:0] wrbk_result1_i,
  // for FPU64
  input                  [NUM_GPRS-1:0] wrbk_rfd2_we1h_i,
  input                                 wrbk_rfd2_we_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] wrbk_rfd2_adr_i,
  input      [OPTION_OPERAND_WIDTH-1:0] wrbk_result2_i,

  // outputs (combinatorial)
  output reg [OPTION_OPERAND_WIDTH-1:0] dcod_rfa1_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] dcod_rfb1_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] dcod_rfa2_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] dcod_rfb2_o,

  // we use adder in EXECUTE to compute return address (pc+8) for l.jl/l.jalr
  input                                 dcod_op_jal_i,
  input      [OPTION_OPERAND_WIDTH-1:0] pc_decode_i,

  // Special case for l.jr/l.jalr
  output     [OPTION_OPERAND_WIDTH-1:0] dcod_rfb1_jr_o
);

  // short names
  localparam RF_AW = OPTION_RF_ADDR_WIDTH;
  localparam RF_DW = OPTION_OPERAND_WIDTH;

  // Declarations
  wire [RF_DW-1:0] gpr0_rdata_bus [NUM_GPRS-1:0];

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

  //----------------------------------//
  // SPR BUS for Group #0 GPRs access //
  //----------------------------------//

  // Group #0 GPRs chip select
  wire spr_gpr0_cs = spr_bus_stb_r &                  // Group #0 GPRs access
                     (spr_bus_addr_r[15:9] == 7'd2) & // Group #0 GPRs access, see OR1K_SPR_GPR0_ADDR
                     (spr_bus_addr_r[ 8:5] == 4'd0);  // Group #0 GPRs access

  // Group #0 GPRs write enables (1-hot coded)
  wire [NUM_GPRS-1:0] spr_gpr0_we;

  // We declare states or SPR BUS FSM here because some
  // of EDA tools deprecate local parameters declaration
  // inside of generate blocks.

  localparam  [3:0] SPR_GPR0_WAITING = 4'b0001,
                    SPR_GPR0_WE_STRB = 4'b0010,
                    SPR_GPR0_READ_MX = 4'b0100,
                    SPR_GPR0_ACK     = 4'b1000;

  generate
  /* verilator lint_off WIDTH */
  if (FEATURE_DEBUGUNIT != "NONE") begin : dbgu_enabled
  /* verilator lint_on WIDTH */

    // SPR BUS FSM states
    reg         [3:0] spr_gpr0_state;

    // Particular states
    wire              spr_gpr0_waiting_state = spr_gpr0_state[0];
    wire              spr_gpr0_read_mx_state = spr_gpr0_state[2];
    assign            spr_bus_ack_gpr0_o     = spr_gpr0_state[3]; // DBGU enabled

    // Write enables
    reg    [NUM_GPRS-1:0] spr_gpr0_we_r;
    assign                spr_gpr0_we = spr_gpr0_we_r; // DBGU enabled

    // Acceess address
    wire    [RF_AW-1:0] spr_gpr0_addr = spr_bus_addr_r[RF_AW-1:0];

    // Read data
    reg     [RF_DW-1:0] spr_bus_dat_gpr0_r;
    assign              spr_bus_dat_gpr0_o = spr_bus_dat_gpr0_r; // DBGU enabled

    // SPR BUS FSM
    always @(posedge cpu_clk) begin
      if (cpu_rst) begin
        spr_gpr0_we_r  <= {NUM_GPRS{1'b0}};
        spr_gpr0_state <= SPR_GPR0_WAITING;
      end
      else begin
        // synthesis parallel_case
        case (spr_gpr0_state)
          // waiting Group #0 GPRs access
          SPR_GPR0_WAITING: begin
            if (spr_gpr0_cs) begin
              spr_gpr0_we_r  <= {{(NUM_GPRS-1){1'b0}},spr_bus_we_l} << spr_gpr0_addr;
              spr_gpr0_state <= spr_bus_we_l ? SPR_GPR0_WE_STRB : SPR_GPR0_READ_MX;
            end
          end

          // write strobe
          SPR_GPR0_WE_STRB: begin
            spr_gpr0_we_r  <= {NUM_GPRS{1'b0}};
            spr_gpr0_state <= SPR_GPR0_ACK;
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
      spr_bus_dat_gpr0_r <= gpr0_rdata_bus[spr_gpr0_addr & {RF_AW{spr_gpr0_read_mx_state}}];
    end

  end
  else begin : dbgu_disabled

    // Write enables
    assign spr_gpr0_we = {NUM_GPRS{1'b0}}; // DBGU disabled

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

  //------------------//
  // GPRs of Group #0 //
  //------------------//

  // GPR[0] is always zero.
  assign gpr0_rdata_bus[0] = {RF_DW{1'b0}};
  
  generate
  genvar ic;
  for (ic = 1; ic < NUM_GPRS; ic = ic + 1) begin: gpr_gen
    // GPR instances
    single_gpr
    #(
      .OPTION_OPERAND_WIDTH (OPTION_OPERAND_WIDTH) // SINGLE GPR
    )
    u_single_gpr
    (
      // clock
      .cpu_clk          (cpu_clk), // SINGLE GPR
      // write back D1
      .wrbk_rfd1_we1h_i (wrbk_rfd1_we1h_i[ic] & (~pipeline_flush_i)), // SINGLE GPR
      .wrbk_result1_i   (wrbk_result1_i), // SINGLE GPR
      // write back D2 for FPU64
      .wrbk_rfd2_we1h_i (wrbk_rfd2_we1h_i[ic] & (~pipeline_flush_i)), // SINGLE GPR
      .wrbk_result2_i   (wrbk_result2_i), // SINGLE GPR
      // write by SPR BUS access
      .spr_gpr0_we_i    (spr_gpr0_we[ic]), // SINGLE GPR
      .spr_gpr0_wdata_i (spr_bus_dat_l), // SINGLE GPR
      // content
      .gpr_o            (gpr0_rdata_bus[ic]) // SINGLE GPR
    );
  end // gpr_gen
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
    wire              spr_gprS_waiting_state = spr_gprS_state[0];
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


  //-----------------------//
  // DECODE stage (dcod_*) //
  //-----------------------//

  // D1A1 and D2A1 forwarding conditions
  //  # WriteBack-to-Fetch
  wire wrb2fth_d1a1_fwd = wrbk_rfd1_we_i & (wrbk_rfd1_adr_i == fetch_rfa1_adr_i);
  wire wrb2fth_d2a1_fwd = wrbk_rfd2_we_i & (wrbk_rfd2_adr_i == fetch_rfa1_adr_i);
  //  # WriteBack-to-Decode
  wire wrb2dec_d1a1_fwd = wrbk_rfd1_we_i & (wrbk_rfd1_adr_i == dcod_rfa1_adr_i);
  wire wrb2dec_d2a1_fwd = wrbk_rfd2_we_i & (wrbk_rfd2_adr_i == dcod_rfa1_adr_i);
  // Registering RFA1-output
  reg [RF_DW-1:0] dcod_rfa1_r;
  // ---
  always @(posedge cpu_clk) begin
    if (padv_dcod_i) begin
      dcod_rfa1_r <= wrb2fth_d1a1_fwd ? wrbk_result1_i :
                     (wrb2fth_d2a1_fwd ? wrbk_result2_i :
                                          gpr0_rdata_bus[fetch_rfa1_adr_i]);
    end
    else begin
      dcod_rfa1_r <= wrb2dec_d1a1_fwd ? wrbk_result1_i :
                     (wrb2dec_d2a1_fwd ? wrbk_result2_i :
                                          dcod_rfa1_r);
    end
  end // at cpu clock
  // Forwarding mux for RFA1-output  
  always @(dcod_op_jal_i    or pc_decode_i    or
           wrb2dec_d1a1_fwd or wrbk_result1_i or
           wrb2dec_d2a1_fwd or wrbk_result2_i or
           dcod_rfa1_r) begin
    // synthesis parallel_case
    casez ({dcod_op_jal_i, wrb2dec_d1a1_fwd, wrb2dec_d2a1_fwd})
      3'b1??:  dcod_rfa1_o = pc_decode_i;
      3'b01?:  dcod_rfa1_o = wrbk_result1_i;
      3'b001:  dcod_rfa1_o = wrbk_result2_i;
      default: dcod_rfa1_o = dcod_rfa1_r;
    endcase
  end

  // D1B1 and D2B1 forwarding conditions
  //  # WriteBack-to-Fetch
  wire wrb2fth_d1b1_fwd = wrbk_rfd1_we_i & (wrbk_rfd1_adr_i == fetch_rfb1_adr_i);
  wire wrb2fth_d2b1_fwd = wrbk_rfd2_we_i & (wrbk_rfd2_adr_i == fetch_rfb1_adr_i);
  //  # WriteBack-to-Decode
  wire wrb2dec_d1b1_fwd = wrbk_rfd1_we_i & (wrbk_rfd1_adr_i == dcod_rfb1_adr_i);
  wire wrb2dec_d2b1_fwd = wrbk_rfd2_we_i & (wrbk_rfd2_adr_i == dcod_rfb1_adr_i);
  // Registering RFB1-output
  reg [RF_DW-1:0] dcod_rfb1_r;
  // ---
  always @(posedge cpu_clk) begin
    if (padv_dcod_i) begin
      dcod_rfb1_r <= wrb2fth_d1b1_fwd ? wrbk_result1_i :
                     (wrb2fth_d2b1_fwd ? wrbk_result2_i :
                                          gpr0_rdata_bus[fetch_rfb1_adr_i]);
    end
    else begin
      dcod_rfb1_r <= wrb2dec_d1b1_fwd ? wrbk_result1_i :
                     (wrb2dec_d2b1_fwd ? wrbk_result2_i :
                                          dcod_rfb1_r);
    end
  end // at cpu clock
  // Forwarding mux RFB1-output
  always @(dcod_op_jal_i        or
           dcod_immediate_sel_i or dcod_immediate_i or
           wrb2dec_d1b1_fwd     or wrbk_result1_i   or
           wrb2dec_d2b1_fwd     or wrbk_result2_i   or
           dcod_rfb1_r) begin
    // synthesis parallel_case
    casez ({dcod_op_jal_i,    dcod_immediate_sel_i,
            wrb2dec_d1b1_fwd, wrb2dec_d2b1_fwd})
      4'b1???: dcod_rfb1_o = 4'd8; // (FEATURE_DELAY_SLOT == "ENABLED")
      4'b01??: dcod_rfb1_o = dcod_immediate_i;
      4'b001?: dcod_rfb1_o = wrbk_result1_i;
      4'b0001: dcod_rfb1_o = wrbk_result2_i;
      default: dcod_rfb1_o = dcod_rfb1_r;
    endcase
  end

  // D1A2 and D2A2 forwarding conditions
  //  # WriteBack-to-Fetch
  wire wrb2fth_d1a2_fwd = wrbk_rfd1_we_i & (wrbk_rfd1_adr_i == fetch_rfa2_adr_i);
  wire wrb2fth_d2a2_fwd = wrbk_rfd2_we_i & (wrbk_rfd2_adr_i == fetch_rfa2_adr_i);
  //  # WriteBack-to-Decode
  wire wrb2dec_d1a2_fwd = wrbk_rfd1_we_i & (wrbk_rfd1_adr_i == dcod_rfa2_adr_i);
  wire wrb2dec_d2a2_fwd = wrbk_rfd2_we_i & (wrbk_rfd2_adr_i == dcod_rfa2_adr_i);
  // Registering RFA2-output
  reg [RF_DW-1:0] dcod_rfa2_r;
  // ---
  always @(posedge cpu_clk) begin
    if (padv_dcod_i) begin
      dcod_rfa2_r <= wrb2fth_d1a2_fwd ? wrbk_result1_i :
                     (wrb2fth_d2a2_fwd ? wrbk_result2_i :
                                          gpr0_rdata_bus[fetch_rfa2_adr_i]);
    end
    else begin
      dcod_rfa2_r <= wrb2dec_d1a2_fwd ? wrbk_result1_i :
                     (wrb2dec_d2a2_fwd ? wrbk_result2_i :
                                          dcod_rfa2_r);
    end
  end // at cpu clock
  // Muxing and forwarding RFA2-output
  always @(wrb2dec_d1a2_fwd or wrbk_result1_i or
           wrb2dec_d2a2_fwd or wrbk_result2_i or
           dcod_rfa2_r) begin
    // synthesis parallel_case
    casez ({wrb2dec_d1a2_fwd, wrb2dec_d2a2_fwd})
      2'b1?:   dcod_rfa2_o = wrbk_result1_i;
      2'b01:   dcod_rfa2_o = wrbk_result2_i;
      default: dcod_rfa2_o = dcod_rfa2_r;
    endcase
  end

  // D1B2 and D2B2 forwarding conditions
  //  # WriteBack-to-Fetch
  wire wrb2fth_d1b2_fwd = wrbk_rfd1_we_i & (wrbk_rfd1_adr_i == fetch_rfb2_adr_i);
  wire wrb2fth_d2b2_fwd = wrbk_rfd2_we_i & (wrbk_rfd2_adr_i == fetch_rfb2_adr_i);
  //  # WriteBack-to-Decode
  wire wrb2dec_d1b2_fwd = wrbk_rfd1_we_i & (wrbk_rfd1_adr_i == dcod_rfb2_adr_i);
  wire wrb2dec_d2b2_fwd = wrbk_rfd2_we_i & (wrbk_rfd2_adr_i == dcod_rfb2_adr_i);
  // Registering RFB2-output
  reg [RF_DW-1:0] dcod_rfb2_r;
  // ---
  always @(posedge cpu_clk) begin
    if (padv_dcod_i) begin
      dcod_rfb2_r <= wrb2fth_d1b2_fwd ? wrbk_result1_i :
                     (wrb2dec_d2b2_fwd ? wrbk_result2_i :
                                          gpr0_rdata_bus[fetch_rfb2_adr_i]);
    end
    else begin
      dcod_rfb2_r <= wrb2dec_d1b2_fwd ? wrbk_result1_i :
                     (wrb2dec_d2b2_fwd ? wrbk_result2_i :
                                          dcod_rfb2_r);
    end
  end // at cpu clock
  // Muxing and forwarding RFB2-output
  always @(wrb2dec_d1b2_fwd or wrbk_result1_i or
           wrb2dec_d2b2_fwd or wrbk_result2_i or
           dcod_rfb2_r) begin
    // synthesis parallel_case
    casez ({wrb2dec_d1b2_fwd, wrb2dec_d2b2_fwd})
      2'b1?:   dcod_rfb2_o = wrbk_result1_i;
      2'b01:   dcod_rfb2_o = wrbk_result2_i;
      default: dcod_rfb2_o = dcod_rfb2_r;
    endcase
  end


  // Special case for l.jr/l.jalr
  //   (a) By default these instructions require B1 operand,
  //       so we implemented simlified path here
  //   (b) The output is used next clock to DECODE to form
  //       registered l.jr/l.jalr command
  //   (c) IFETCH generates bubbles till B1 completion
  assign dcod_rfb1_jr_o = dcod_rfb1_r;

endmodule // mor1kx_rf_marocchino
