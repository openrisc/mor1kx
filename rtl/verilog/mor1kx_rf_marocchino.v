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
//   Copyright (C) 2015-2016 Andrey Bacherov                        //
//                           avbacherov@opencores.org               //
//                                                                  //
//      This Source Code Form is subject to the terms of the        //
//      Open Hardware Description License, v. 1.0. If a copy        //
//      of the OHDL was not distributed with this file, You         //
//      can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt     //
//                                                                  //
//////////////////////////////////////////////////////////////////////

`include "mor1kx-defines.v"

module mor1kx_rf_marocchino
#(
  parameter OPTION_RF_CLEAR_ON_INIT  = 0,
  parameter OPTION_RF_ADDR_WIDTH     = 5,
  parameter FEATURE_DEBUGUNIT        = "NONE",
  parameter OPTION_OPERAND_WIDTH     = 32
)
(
  input                             clk,
  input                             rst,

  // pipeline control signals
  input                             pipeline_flush_i,
  input                             padv_fetch_i,

  // SPR bus
  input                          [15:0] spr_bus_addr_i,
  input                                 spr_bus_stb_i,
  input                                 spr_bus_we_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_i,
  output reg                            spr_bus_ack_gpr_o,
  output     [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_gpr_o,

  // from FETCH
  input  [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfa1_adr_i,
  input  [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfb1_adr_i,
  // for FPU64
  input  [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfa2_adr_i,
  input  [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfb2_adr_i,

  // from DECODE
  input                             dcod_rfa1_req_i,
  input  [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa1_adr_i,
  input                             dcod_rfb1_req_i,
  input  [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb1_adr_i,
  input  [OPTION_OPERAND_WIDTH-1:0] dcod_immediate_i,
  input                             dcod_immediate_sel_i,
  // for FPU64
  input                             dcod_rfa2_req_i,
  input  [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa2_adr_i,
  input                             dcod_rfb2_req_i,
  input  [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb2_adr_i,

  // from WB
  input                             wb_rfd1_wb_i,
  input  [OPTION_RF_ADDR_WIDTH-1:0] wb_rfd1_adr_i,
  input  [OPTION_OPERAND_WIDTH-1:0] wb_result1_i,
  // for FPU64
  input                             wb_rfd2_wb_i,
  input  [OPTION_RF_ADDR_WIDTH-1:0] wb_rfd2_adr_i,
  input  [OPTION_OPERAND_WIDTH-1:0] wb_result2_i,

  // D1 related WB-to-DECODE hazards for LSU WB miss processing
  output                            dcod_wb2dec_eq_adr_d1a1_o,
  output                            dcod_wb2dec_eq_adr_d1b1_o,
  output                            dcod_wb2dec_eq_adr_d1a2_o,
  output                            dcod_wb2dec_eq_adr_d1b2_o,

  // outputs
  output [OPTION_OPERAND_WIDTH-1:0] dcod_rfa1_o,
  output [OPTION_OPERAND_WIDTH-1:0] dcod_rfb1_o,
  output [OPTION_OPERAND_WIDTH-1:0] dcod_rfa2_o,
  output [OPTION_OPERAND_WIDTH-1:0] dcod_rfb2_o,

  // we use adder for l.jl/l.jalr to compute return address: (pc+8)
  input                             dcod_op_jal_i,
  input  [OPTION_OPERAND_WIDTH-1:0] pc_decode_i,

  // Special case for l.jr/l.jalr
  output [OPTION_OPERAND_WIDTH-1:0] dcod_rfb1_jr_o
);

  // short names
  localparam RF_AW = OPTION_RF_ADDR_WIDTH;
  localparam RF_DW = OPTION_OPERAND_WIDTH;


  //-----------//
  // FETCH->RF //
  //-----------//

  // ram blocks outputs
  wire [(RF_DW-1):0] rfa_even_dout;
  wire [(RF_DW-1):0] rfa_odd_dout;
  wire [(RF_DW-1):0] rfb_even_dout;
  wire [(RF_DW-1):0] rfb_odd_dout;

  // SPR/GPR access from bus signals
  wire spr_gpr_we;
  wire spr_gpr_cs;


  // short name for read request
  wire read_req = padv_fetch_i;


  // 1-clock witting strobes for GPR write
  //  - writting act could be blocked by exceptions processing
  //    because the istruction isn't completed and
  //    will be restarted by l.rfe

  //  write in even
  wire write_even_req = (wb_rfd1_wb_i & ~wb_rfd1_adr_i[0]) | (wb_rfd2_wb_i & ~wb_rfd2_adr_i[0]) | (spr_gpr_we & ~spr_bus_addr_i[0]);
  // write in odd
  wire write_odd_req  = (wb_rfd1_wb_i &  wb_rfd1_adr_i[0]) | (wb_rfd2_wb_i &  wb_rfd2_adr_i[0]) | (spr_gpr_we &  spr_bus_addr_i[0]);


  // even/odd multiplexing of input addresses and data
  //  if A(B)'s address is odd than A2(B2)=A(B)+1 is even and vise verse

  //    operand A-even address
  wire [(RF_AW-1):0] fetch_rfa_even_addr = fetch_rfa1_adr_i[0] ? fetch_rfa2_adr_i : fetch_rfa1_adr_i;
  //    operand A-odd address
  wire [(RF_AW-1):0] fetch_rfa_odd_addr  = fetch_rfa1_adr_i[0] ? fetch_rfa1_adr_i : fetch_rfa2_adr_i;

  //    operand B-even address
  wire [(RF_AW-1):0] fetch_rfb_even_addr = fetch_rfb1_adr_i[0] ? fetch_rfb2_adr_i : fetch_rfb1_adr_i;
  //    operand B-odd address
  wire [(RF_AW-1):0] fetch_rfb_odd_addr  = fetch_rfb1_adr_i[0] ? fetch_rfb1_adr_i : fetch_rfb2_adr_i;

  //    Write Back even address & data
  wire [(RF_AW-1):0] wb_even_addr = wb_rfd1_adr_i[0] ? wb_rfd2_adr_i : wb_rfd1_adr_i;
  wire [(RF_DW-1):0] wb_even_data = wb_rfd1_adr_i[0] ? wb_result2_i  : wb_result1_i;
  //    Write Back odd address & data
  wire [(RF_AW-1):0] wb_odd_addr = wb_rfd1_adr_i[0] ? wb_rfd1_adr_i : wb_rfd2_adr_i;
  wire [(RF_DW-1):0] wb_odd_data = wb_rfd1_adr_i[0] ? wb_result1_i  : wb_result2_i;

  //  write even address & data
  wire [(RF_AW-1):0] write_even_addr = spr_gpr_we ? spr_bus_addr_i[(RF_AW-1):0] : wb_even_addr;
  wire [(RF_DW-1):0] write_even_data = spr_gpr_we ? spr_bus_dat_i               : wb_even_data;
  //  write odd address & data
  wire [(RF_AW-1):0] write_odd_addr = spr_gpr_we ? spr_bus_addr_i[(RF_AW-1):0] : wb_odd_addr;
  wire [(RF_DW-1):0] write_odd_data = spr_gpr_we ? spr_bus_dat_i               : wb_odd_data;


  // Controls for A-even RAM block
  //  # read/write conflict
  wire rfa_even_hazard = (write_even_req &  read_req &  (write_even_addr == fetch_rfa_even_addr)) |
                         (write_even_req & ~read_req & ((write_even_addr == dcod_rfa1_adr_i) |
                                                        (write_even_addr == dcod_rfa2_adr_i)));
  //  # signals for Read/Write port *_rwp_*
  wire               rfa_even_rwp_en   = rfa_even_hazard | read_req;
  wire               rfa_even_rwp_we   = rfa_even_hazard;
  wire [(RF_AW-2):0] rfa_even_rwp_addr = rfa_even_hazard ? write_even_addr[(RF_AW-1):1] : fetch_rfa_even_addr[(RF_AW-1):1];
  //  # signals for Write port *_wp_*
  wire rfa_even_wp_en = write_even_req & ~rfa_even_hazard;
  //  # RFA-even RAM-block instance
  mor1kx_dpram_en_w1st_sclk
  #(
    .ADDR_WIDTH     (RF_AW-1),
    .DATA_WIDTH     (RF_DW),
    .CLEAR_ON_INIT  (OPTION_RF_CLEAR_ON_INIT)
  )
  rfa_even
  (
    // common clock
    .clk    (clk),
    // port "a": Read / Write (for RW-conflict case)
    .en_a   (rfa_even_rwp_en & ~pipeline_flush_i),
    .we_a   (rfa_even_rwp_we),
    .addr_a (rfa_even_rwp_addr),
    .din_a  (write_even_data),
    .dout_a (rfa_even_dout),
    // port "b": Write if no RW-conflict
    .en_b   (rfa_even_wp_en & ~pipeline_flush_i),
    .we_b   (write_even_req),
    .addr_b (write_even_addr[(RF_AW-1):1]),
    .din_b  (write_even_data),
    .dout_b ()
  );


  // Controls for A-odd RAM block
  //  # read/write conflict
  wire rfa_odd_hazard = (write_odd_req &  read_req &  (write_odd_addr == fetch_rfa_odd_addr)) |
                        (write_odd_req & ~read_req & ((write_odd_addr == dcod_rfa1_adr_i) |
                                                      (write_odd_addr == dcod_rfa2_adr_i)));
  //  # signals for Read/Write port *_rwp_*
  wire               rfa_odd_rwp_en   = rfa_odd_hazard | read_req;
  wire               rfa_odd_rwp_we   = rfa_odd_hazard;
  wire [(RF_AW-2):0] rfa_odd_rwp_addr = rfa_odd_hazard ? write_odd_addr[(RF_AW-1):1] : fetch_rfa_odd_addr[(RF_AW-1):1];
  //  # signals for Write port *_wp_*
  wire rfa_odd_wp_en = write_odd_req & ~rfa_odd_hazard;
  //  # RFA-odd RAM-block instance
  mor1kx_dpram_en_w1st_sclk
  #(
    .ADDR_WIDTH     (RF_AW-1),
    .DATA_WIDTH     (RF_DW),
    .CLEAR_ON_INIT  (OPTION_RF_CLEAR_ON_INIT)
  )
  rfa_odd
  (
    // common clock
    .clk    (clk),
    // port "a": Read / Write (for RW-conflict case)
    .en_a   (rfa_odd_rwp_en & ~pipeline_flush_i),
    .we_a   (rfa_odd_rwp_we),
    .addr_a (rfa_odd_rwp_addr),
    .din_a  (write_odd_data),
    .dout_a (rfa_odd_dout),
    // port "b": Write if no RW-conflict
    .en_b   (rfa_odd_wp_en & ~pipeline_flush_i),
    .we_b   (write_odd_req),
    .addr_b (write_odd_addr[(RF_AW-1):1]),
    .din_b  (write_odd_data),
    .dout_b ()
  );


  // Controls for B-even RAM block
  //  # read/write conflict
  wire rfb_even_hazard = (write_even_req &  read_req &  (write_even_addr == fetch_rfb_even_addr)) |
                         (write_even_req & ~read_req & ((write_even_addr == dcod_rfb1_adr_i) |
                                                        (write_even_addr == dcod_rfb2_adr_i)));
  //  # signals for Read/Write port *_rwp_*
  wire               rfb_even_rwp_en   = rfb_even_hazard | read_req;
  wire               rfb_even_rwp_we   = rfb_even_hazard;
  wire [(RF_AW-2):0] rfb_even_rwp_addr = rfb_even_hazard ? write_even_addr[(RF_AW-1):1] : fetch_rfb_even_addr[(RF_AW-1):1];
  //  # signals for Write port *_wp_*
  wire rfb_even_wp_en = write_even_req & ~rfb_even_hazard;
  //  # RFA-even RAM-block instance
  mor1kx_dpram_en_w1st_sclk
  #(
    .ADDR_WIDTH     (RF_AW-1),
    .DATA_WIDTH     (RF_DW),
    .CLEAR_ON_INIT  (OPTION_RF_CLEAR_ON_INIT)
  )
  rfb_even
  (
    // common clock
    .clk    (clk),
    // port "a": Read / Write (for RW-conflict case)
    .en_a   (rfb_even_rwp_en & ~pipeline_flush_i),
    .we_a   (rfb_even_rwp_we),
    .addr_a (rfb_even_rwp_addr),
    .din_a  (write_even_data),
    .dout_a (rfb_even_dout),
    // port "b": Write if no RW-conflict
    .en_b   (rfb_even_wp_en & ~pipeline_flush_i),
    .we_b   (write_even_req),
    .addr_b (write_even_addr[(RF_AW-1):1]),
    .din_b  (write_even_data),
    .dout_b ()
  );


  // Controls for B-odd RAM block
  //  # read/write conflict
  wire rfb_odd_hazard = (write_odd_req &  read_req &  (write_odd_addr == fetch_rfb_odd_addr)) |
                        (write_odd_req & ~read_req & ((write_odd_addr == dcod_rfb1_adr_i) |
                                                      (write_odd_addr == dcod_rfb2_adr_i)));
  //  # signals for Read/Write port *_rwp_*
  wire               rfb_odd_rwp_en   = rfb_odd_hazard | read_req;
  wire               rfb_odd_rwp_we   = rfb_odd_hazard;
  wire [(RF_AW-2):0] rfb_odd_rwp_addr = rfb_odd_hazard ? write_odd_addr[(RF_AW-1):1] : fetch_rfb_odd_addr[(RF_AW-1):1];
  //  # signals for Write port *_wp_*
  wire rfb_odd_wp_en = write_odd_req & ~rfb_odd_hazard;
  //  # RFA-odd RAM-block instance
  mor1kx_dpram_en_w1st_sclk
  #(
    .ADDR_WIDTH     (RF_AW-1),
    .DATA_WIDTH     (RF_DW),
    .CLEAR_ON_INIT  (OPTION_RF_CLEAR_ON_INIT)
  )
  rfb_odd
  (
    // common clock
    .clk    (clk),
    // port "a": Read / Write (for RW-conflict case)
    .en_a   (rfb_odd_rwp_en & ~pipeline_flush_i),
    .we_a   (rfb_odd_rwp_we),
    .addr_a (rfb_odd_rwp_addr),
    .din_a  (write_odd_data),
    .dout_a (rfb_odd_dout),
    // port "b": Write if no RW-conflict
    .en_b   (rfb_odd_wp_en & ~pipeline_flush_i),
    .we_b   (write_odd_req),
    .addr_b (write_odd_addr[(RF_AW-1):1]),
    .din_b  (write_odd_data),
    .dout_b ()
  );


  //---------------//
  // SPR interface //
  //---------------//

  // detect GPR access
  //  !!! low bits of SPR-address are used for addressing RF !!!
  assign spr_gpr_cs = spr_bus_stb_i & (spr_bus_addr_i[15:10] == 6'b000001); // see OR1K_SPR_GPR0_ADDR

  generate
  /* verilator lint_off WIDTH */
  if (FEATURE_DEBUGUNIT != "NONE") begin : rfspr_enabled
  /* verilator lint_on WIDTH */

    wire [(RF_DW-1):0] rfspr_dout;

    //  we don't expect R/W-collisions for SPRbus vs WB cycles since
    //    SPRbus access start 1-clock later than WB
    //    thanks to MT(F)SPR processing logic (see OMAN)

    reg               spr_gpr_we_r;
    reg               spr_gpr_re_r;
    reg               spr_gpr_mux_r;
    reg [(RF_DW-1):0] spr_bus_dat_gpr_r;

    // SPR processing cycle
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst) begin
        spr_gpr_we_r      <= 1'b0;
        spr_gpr_re_r      <= 1'b0;
        spr_gpr_mux_r     <= 1'b0;
        spr_bus_ack_gpr_o <= 1'b0;
        spr_bus_dat_gpr_r <= {RF_DW{1'b0}};
      end
      else if (spr_bus_ack_gpr_o) begin
        spr_gpr_we_r      <= 1'b0;
        spr_gpr_re_r      <= 1'b0;
        spr_gpr_mux_r     <= 1'b0;
        spr_bus_ack_gpr_o <= 1'b0;
        spr_bus_dat_gpr_r <= {RF_DW{1'b0}};
      end
      else if (spr_gpr_mux_r) begin
        spr_gpr_we_r      <= 1'b0;
        spr_gpr_re_r      <= 1'b0;
        spr_gpr_mux_r     <= 1'b0;
        spr_bus_ack_gpr_o <= 1'b1;
        spr_bus_dat_gpr_r <= rfspr_dout;
      end
      else if (spr_gpr_re_r) begin
        spr_gpr_we_r      <= 1'b0;
        spr_gpr_re_r      <= 1'b0;
        spr_gpr_mux_r     <= 1'b1;
        spr_bus_ack_gpr_o <= 1'b0;
        spr_bus_dat_gpr_r <= {RF_DW{1'b0}};
      end
      else if (spr_gpr_cs) begin
        spr_gpr_we_r      <= spr_bus_we_i;
        spr_gpr_re_r      <= ~spr_bus_we_i;
        spr_gpr_mux_r     <= 1'b0;
        spr_bus_ack_gpr_o <= spr_bus_we_i; // write on next posedge of clock and finish
        spr_bus_dat_gpr_r <= {RF_DW{1'b0}};
      end
    end // @ clock

    assign spr_gpr_we        = spr_gpr_we_r;
    assign spr_bus_dat_gpr_o = spr_bus_dat_gpr_r;

    // for port #1 we write result #1 and read by debug unit
    wire               rfspr_p1_we    = wb_rfd1_wb_i | spr_gpr_we;
    wire [(RF_AW-1):0] rfspr_p1_addr  = wb_rfd1_wb_i ? wb_rfd1_adr_i : spr_bus_addr_i[(RF_AW-1):0];
    wire [(RF_DW-1):0] rfspr_p1_data  = wb_rfd1_wb_i ? wb_result1_i  : spr_bus_dat_i;

    // ---
    mor1kx_dpram_en_w1st_sclk
    #(
      .ADDR_WIDTH     (RF_AW),
      .DATA_WIDTH     (RF_DW),
      .CLEAR_ON_INIT  (OPTION_RF_CLEAR_ON_INIT)
    )
    rfspr
    (
      // common clock
      .clk    (clk),
      // port "a"
      .en_a   ((rfspr_p1_we | spr_gpr_re_r) & ~pipeline_flush_i),
      .we_a   (rfspr_p1_we),
      .addr_a (rfspr_p1_addr),
      .din_a  (rfspr_p1_data),
      .dout_a (rfspr_dout),
      // port "b": just write result #2
      .en_b   (wb_rfd2_wb_i & ~pipeline_flush_i),
      .we_b   (wb_rfd2_wb_i),
      .addr_b (wb_rfd2_adr_i),
      .din_b  (wb_result2_i),
      .dout_b ()
    );

  end
  else begin : rfspr_disabled

    // make ACK
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        spr_bus_ack_gpr_o <= 1'b0;
      else if (spr_bus_ack_gpr_o)
        spr_bus_ack_gpr_o <= 1'b0;
      else if (spr_gpr_cs)
        spr_bus_ack_gpr_o <= 1'b1;
    end

    // SPR data output
    assign spr_bus_dat_gpr_o = {RF_DW{1'b0}};

    // Write by SPR-bus command
    assign spr_gpr_we = 1'b0;

  end
  endgenerate


  //-----------------------//
  // DECODE stage (dcod_*) //
  //-----------------------//

  // Common WB-to-DECODE hazards detection (sorted by detsination)
  //  # D1 related
  assign dcod_wb2dec_eq_adr_d1a1_o = (wb_rfd1_adr_i == dcod_rfa1_adr_i);
  wire   dcod_wb2dec_hazard_d1a1   = dcod_wb2dec_eq_adr_d1a1_o & wb_rfd1_wb_i & dcod_rfa1_req_i;
  //---
  assign dcod_wb2dec_eq_adr_d1b1_o = (wb_rfd1_adr_i == dcod_rfb1_adr_i);
  wire   dcod_wb2dec_hazard_d1b1   = dcod_wb2dec_eq_adr_d1b1_o & wb_rfd1_wb_i & dcod_rfb1_req_i;
  //---
  assign dcod_wb2dec_eq_adr_d1a2_o = (wb_rfd1_adr_i == dcod_rfa2_adr_i);
  wire   dcod_wb2dec_hazard_d1a2   = dcod_wb2dec_eq_adr_d1a2_o & wb_rfd1_wb_i & dcod_rfa2_req_i;
  //---
  assign dcod_wb2dec_eq_adr_d1b2_o = (wb_rfd1_adr_i == dcod_rfb2_adr_i);
  wire   dcod_wb2dec_hazard_d1b2   = dcod_wb2dec_eq_adr_d1b2_o & wb_rfd1_wb_i & dcod_rfb2_req_i;
  //  # D2 related
  wire dcod_wb2dec_hazard_d2a1 = (wb_rfd2_adr_i == dcod_rfa1_adr_i) & wb_rfd2_wb_i & dcod_rfa1_req_i;
  wire dcod_wb2dec_hazard_d2b1 = (wb_rfd2_adr_i == dcod_rfb1_adr_i) & wb_rfd2_wb_i & dcod_rfb1_req_i;
  wire dcod_wb2dec_hazard_d2a2 = (wb_rfd2_adr_i == dcod_rfa2_adr_i) & wb_rfd2_wb_i & dcod_rfa2_req_i;
  wire dcod_wb2dec_hazard_d2b2 = (wb_rfd2_adr_i == dcod_rfb2_adr_i) & wb_rfd2_wb_i & dcod_rfb2_req_i;


  // Muxing and forwarding RFA1-output
  assign dcod_rfa1_o = dcod_op_jal_i           ? pc_decode_i  :
                       dcod_wb2dec_hazard_d1a1 ? wb_result1_i :
                       dcod_wb2dec_hazard_d2a1 ? wb_result2_i :
                       dcod_rfa1_adr_i[0]      ? rfa_odd_dout :
                                                 rfa_even_dout;

  // Muxing and forwarding RFB1-output
  assign dcod_rfb1_o = dcod_op_jal_i           ? 4'd8             : // (FEATURE_DELAY_SLOT == "ENABLED")
                       dcod_immediate_sel_i    ? dcod_immediate_i :
                       dcod_wb2dec_hazard_d1b1 ? wb_result1_i     :
                       dcod_wb2dec_hazard_d2b1 ? wb_result2_i     :
                       dcod_rfb1_adr_i[0]      ? rfb_odd_dout     :
                                                 rfb_even_dout;

  // Muxing and forwarding RFA2-output
  assign dcod_rfa2_o = dcod_wb2dec_hazard_d1a2 ? wb_result1_i :
                       dcod_wb2dec_hazard_d2a2 ? wb_result2_i :
                       dcod_rfa2_adr_i[0]      ? rfa_odd_dout :
                                                 rfa_even_dout;

  // Muxing and forwarding RFB2-output
  assign dcod_rfb2_o = dcod_wb2dec_hazard_d1b2 ? wb_result1_i :
                       dcod_wb2dec_hazard_d2b2 ? wb_result2_i :
                       dcod_rfb2_adr_i[0]      ? rfb_odd_dout :
                                                 rfb_even_dout;


  // Special case for l.jr/l.jalr
  //   (a) by default these instructions require B1 operand, so we implemented
  //       simlified multiplexor here.
  //   (b) the output is used next time in DECODE to form final branch target
  //   (c) in OMAN pipeline is stalled till B1 completion
  wire   dcod_wb2dec_hazard_d1b1_jr = dcod_wb2dec_eq_adr_d1b1_o & wb_rfd1_wb_i;
  // ---
  assign dcod_rfb1_jr_o = dcod_wb2dec_hazard_d1b1_jr ? wb_result1_i :
                          dcod_rfb1_adr_i[0]         ? rfb_odd_dout :
                                                       rfb_even_dout;

endmodule // mor1kx_rf_marocchino
