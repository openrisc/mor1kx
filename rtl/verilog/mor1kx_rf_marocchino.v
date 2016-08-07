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
//   Copyright (C) 2015 Andrey Bacherov                             //
//                      avbacherov@opencores.org                    //
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

  // SPR bus
  input                          [15:0] spr_bus_addr_i,
  input                                 spr_bus_stb_i,
  input                                 spr_bus_we_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_i,
  output reg                            spr_bus_ack_gpr_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_gpr_o,

  // from FETCH
  input                             fetch_rf_adr_valid_i,
  input  [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfa_adr_i,
  input  [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfb_adr_i,

  // from DECODE
  input                             dcod_rfa_req_i,
  input  [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa_adr_i,
  input                             dcod_rfb_req_i,
  input  [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb_adr_i,
  input  [OPTION_OPERAND_WIDTH-1:0] dcod_immediate_i,
  input                             dcod_immediate_sel_i,

  // from WB
  input                             wb_rf_wb_i,
  input  [OPTION_RF_ADDR_WIDTH-1:0] wb_rfd_adr_i,
  input  [OPTION_OPERAND_WIDTH-1:0] wb_result_i,

  // outputs
  output [OPTION_OPERAND_WIDTH-1:0] dcod_rfa_o,
  output [OPTION_OPERAND_WIDTH-1:0] dcod_rfb_o
);

  //-----------//
  // FETCH->RF //
  //-----------//

  // ram blocks controls
  wire [OPTION_OPERAND_WIDTH-1:0] rfa_dout;
  wire [OPTION_OPERAND_WIDTH-1:0] rfb_dout;

  // SPR/GPR access from bus signals
  reg  spr_gpr_we_r;
  wire spr_gpr_cs;


  // 1-clock strobe for GPR write
  //  - writting act could be blocked by exceptions processing
  //    because the istruction isn't completed and
  //    will be restarted by l.rfe
  wire wb_rf_we = wb_rf_wb_i & ~pipeline_flush_i;


  // operand A read/write request attributes
  //  # read request attributes
  wire                            opa_read_req  = fetch_rf_adr_valid_i;
  wire [OPTION_RF_ADDR_WIDTH-1:0] opa_read_addr = fetch_rfa_adr_i;
  //  # read request attributes
  wire                            opa_write_req  = wb_rf_we | spr_gpr_we_r;
  wire [OPTION_RF_ADDR_WIDTH-1:0] opa_write_addr = wb_rf_we ? wb_rfd_adr_i : spr_bus_addr_i;
  wire [OPTION_OPERAND_WIDTH-1:0] opa_write_data = wb_rf_we ? wb_result_i  : spr_bus_dat_i;

  // operand A read/write conflict
  wire opa_rw_hazard = (opa_write_req &  opa_read_req & (opa_write_addr == opa_read_addr)) |
                       (wb_rf_we      & ~opa_read_req & (wb_rfd_adr_i == dcod_rfa_adr_i));

  // operand A form control signals for Read/Write port rwp_*
  wire                            opa_rwp_en    = opa_read_req | opa_rw_hazard;
  wire                            opa_rwp_write = opa_rw_hazard;
  wire [OPTION_RF_ADDR_WIDTH-1:0] opa_rwp_addr  = opa_rw_hazard ? opa_write_addr : opa_read_addr;

  // operand A form control signals for Write port wp_*
  wire opa_wp_en    = opa_write_req & ~opa_rw_hazard;

  // instance RF-A
  mor1kx_dpram_en_w1st_sclk
  #(
    .ADDR_WIDTH     (OPTION_RF_ADDR_WIDTH),
    .DATA_WIDTH     (OPTION_OPERAND_WIDTH),
    .CLEAR_ON_INIT  (OPTION_RF_CLEAR_ON_INIT)
  )
  rfa
  (
    // common clock
    .clk (clk),
    // port "a": Read / Write (for RW-conflict case)
    .en_a   (opa_rwp_en),     // enable port "a"
    .we_a   (opa_rwp_write),  // operation is "write"
    .addr_a (opa_rwp_addr),
    .din_a  (opa_write_data),
    .dout_a (rfa_dout),
    // port "b": Write if no RW-conflict
    .en_b   (opa_wp_en),      // enable port "b"
    .we_b   (opa_wp_en),      // operation is "write"
    .addr_b (opa_write_addr),
    .din_b  (opa_write_data),
    .dout_b ()                // not used
  );


  // operand B read/write request attributes
  //  # read request attributes
  wire                            opb_read_req  = fetch_rf_adr_valid_i;
  wire [OPTION_RF_ADDR_WIDTH-1:0] opb_read_addr = fetch_rfb_adr_i;
  //  # read request attributes
  wire                            opb_write_req  = wb_rf_we | spr_gpr_we_r;
  wire [OPTION_RF_ADDR_WIDTH-1:0] opb_write_addr = wb_rf_we ? wb_rfd_adr_i : spr_bus_addr_i;
  wire [OPTION_OPERAND_WIDTH-1:0] opb_write_data = wb_rf_we ? wb_result_i  : spr_bus_dat_i;

  // operand B read/write conflict
  wire opb_rw_hazard = (opb_write_req &  opb_read_req & (opb_read_addr == opb_write_addr)) |
                       (wb_rf_we      & ~opb_read_req & (wb_rfd_adr_i == dcod_rfb_adr_i));

  // operand B form control signals for Read/Write port rwp_*
  wire                            opb_rwp_en    = opb_read_req | opb_rw_hazard;
  wire                            opb_rwp_write = opb_rw_hazard;
  wire [OPTION_RF_ADDR_WIDTH-1:0] opb_rwp_addr  = opb_rw_hazard ? opb_write_addr : opb_read_addr;

  // operand B form control signals for Write port wp_*
  wire opb_wp_en    = opb_write_req & ~opb_rw_hazard;

  // instance RF-B
  mor1kx_dpram_en_w1st_sclk
  #(
    .ADDR_WIDTH     (OPTION_RF_ADDR_WIDTH),
    .DATA_WIDTH     (OPTION_OPERAND_WIDTH),
    .CLEAR_ON_INIT  (OPTION_RF_CLEAR_ON_INIT)
  )
  rfb
  (
    // common clock
    .clk (clk),
    // port "a": Read / Write (for RW-conflict case)
    .en_a   (opb_rwp_en),     // enable port "a"
    .we_a   (opb_rwp_write),  // operation is "write"
    .addr_a (opb_rwp_addr),
    .din_a  (opb_write_data),
    .dout_a (rfb_dout),
    // port "b": Write if no RW-conflict
    .en_b   (opb_wp_en),      // enable port "b"
    .we_b   (opb_wp_en),      // operation is "write"
    .addr_b (opb_write_addr),
    .din_b  (opb_write_data),
    .dout_b ()                // not used
  );


  //---------------//
  // SPR interface //
  //---------------//

  // detect GPR access
  assign spr_gpr_cs = spr_bus_stb_i & (spr_bus_addr_i == `OR1K_SPR_GPR0_ADDR);

  generate
  /* verilator lint_off WIDTH */
  if (FEATURE_DEBUGUNIT != "NONE") begin : rfspr_gen
  /* verilator lint_on WIDTH */

    wire [OPTION_OPERAND_WIDTH-1:0] rfspr_dout;

    //  we don't expect R/W-collisions for SPRbus vs WB cycles since 
    //    SPRbus access start 1-clock later than WB
    //    thanks to MT(F)SPR processing logic (see OMAN)

    reg spr_gpr_re_r;
    reg spr_gpr_mux_r;
  
    // SPR processing cycle
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst) begin
        spr_gpr_we_r      <= 1'b0;
        spr_gpr_re_r      <= 1'b0;
        spr_gpr_mux_r     <= 1'b0;
        spr_bus_ack_gpr_o <= 1'b0;
        spr_bus_dat_gpr_o <= {OPTION_OPERAND_WIDTH{1'b0}};
      end
      else if (spr_bus_ack_gpr_o) begin
        spr_gpr_we_r      <= 1'b0;
        spr_gpr_re_r      <= 1'b0;
        spr_gpr_mux_r     <= 1'b0;
        spr_bus_ack_gpr_o <= 1'b0;
        spr_bus_dat_gpr_o <= {OPTION_OPERAND_WIDTH{1'b0}};
      end
      else if (spr_gpr_mux_r) begin
        spr_gpr_we_r      <= 1'b0;
        spr_gpr_re_r      <= 1'b0;
        spr_gpr_mux_r     <= 1'b0;
        spr_bus_ack_gpr_o <= 1'b1;
        spr_bus_dat_gpr_o <= rfspr_dout;
      end
      else if (spr_gpr_re_r) begin
        spr_gpr_we_r      <= 1'b0;
        spr_gpr_re_r      <= 1'b0;
        spr_gpr_mux_r     <= 1'b1;
        spr_bus_ack_gpr_o <= 1'b0;
        spr_bus_dat_gpr_o <= {OPTION_OPERAND_WIDTH{1'b0}};
      end
      else if (spr_gpr_cs) begin
        spr_gpr_we_r      <= spr_bus_we_i;
        spr_gpr_re_r      <= ~spr_bus_we_i;
        spr_gpr_mux_r     <= 1'b0;
        spr_bus_ack_gpr_o <= spr_bus_we_i; // write on next posedge of clock and finish
        spr_bus_dat_gpr_o <= {OPTION_OPERAND_WIDTH{1'b0}};
      end
    end // @ clock
  
    wire                            rfspr_wren = wb_rf_we | spr_gpr_we_r;
    wire [OPTION_RF_ADDR_WIDTH-1:0] rfspr_addr = wb_rf_we ? wb_rfd_adr_i : spr_bus_addr_i;
    wire [OPTION_OPERAND_WIDTH-1:0] rfspr_din  = wb_rf_we ? wb_result_i  : spr_bus_dat_i;
  
    mor1kx_spram_en_w1st
    #(
       .ADDR_WIDTH    (OPTION_RF_ADDR_WIDTH),
       .DATA_WIDTH    (OPTION_OPERAND_WIDTH),
       .CLEAR_ON_INIT (OPTION_RF_CLEAR_ON_INIT)
    )
    rfspr
    (
      // clock
      .clk  (clk),
      // port
      .en   (rfspr_wren | spr_gpr_re_r), // enable port
      .we   (rfspr_wren),
      .addr (rfspr_addr),
      .din  (rfspr_din),
      .dout (rfspr_dout)
    );

  end
  else begin

    // make ACK
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        spr_bus_ack_gpr_o <= 1'b0;
      else if (spr_bus_ack_gpr_o)
        spr_bus_ack_gpr_o <= 1'b0;
      else if (spr_gpr_cs)
        spr_bus_ack_gpr_o <= 1'b1;
    end

    // data to output
    always @(posedge clk) begin
      spr_gpr_we_r      <= 1'b0;
      spr_bus_dat_gpr_o <= {OPTION_OPERAND_WIDTH{1'b0}};
    end

  end
  endgenerate


  //-----------------------//
  // DECODE stage (dcod_*) //
  //-----------------------//

  //  WB-to-DECODE hazard
  wire dcod_wb2dec_hazard_a = wb_rf_we & dcod_rfa_req_i & (wb_rfd_adr_i == dcod_rfa_adr_i);
  wire dcod_wb2dec_hazard_b = wb_rf_we & dcod_rfb_req_i & (wb_rfd_adr_i == dcod_rfb_adr_i);

  assign dcod_rfa_o = dcod_wb2dec_hazard_a ? wb_result_i :
                                             rfa_dout;

  assign dcod_rfb_o = dcod_immediate_sel_i ? dcod_immediate_i :
                      dcod_wb2dec_hazard_b ? wb_result_i      :
                                             rfb_dout;

endmodule // mor1kx_rf_marocchino
