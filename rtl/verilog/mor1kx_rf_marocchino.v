/* ****************************************************************************
  This Source Code Form is subject to the terms of the
  Open Hardware Description License, v. 1.0. If a copy
  of the OHDL was not distributed with this file, You
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description:
    Register file for MAROCCHINO pipeline
    Handles reading the register file rams and register bypassing.
    Derived from mor1kx_rf_cappuccino

  Copyright (C) 2012 Julius Baxter <juliusbaxter@gmail.com>
  Copyright (C) 2012-2014 Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>
  Copyright (C) 2015 Andrey Bacherov <avbacherov@opencores.org>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_rf_marocchino
#(
  parameter FEATURE_FASTCONTEXTS     = "NONE",
  parameter OPTION_RF_NUM_SHADOW_GPR = 0,
  parameter OPTION_RF_CLEAR_ON_INIT  = 0,
  parameter OPTION_RF_ADDR_WIDTH     = 5,
  parameter FEATURE_DEBUGUNIT        = "NONE",
  parameter OPTION_OPERAND_WIDTH     = 32
)
(
  input                             clk,
  input                             rst,

  // pipeline control signals
  input                             padv_decode_i,
  input                             exec_new_input_i, // 1-clock delayed of padv-decode
  input                             wb_new_result_i, // 1-clock delayed of padv-wb
  input                             pipeline_flush_i,

  // SPR bus
  input [15:0]                      spr_bus_addr_i,
  input                             spr_bus_stb_i,
  input                             spr_bus_we_i,
  input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_i,
  output                            spr_gpr_ack_o,
  output [OPTION_OPERAND_WIDTH-1:0] spr_gpr_dat_o,

  // from FETCH
  input                             fetch_rf_adr_valid_i,
  input [OPTION_RF_ADDR_WIDTH-1:0]  fetch_rfa_adr_i,
  input [OPTION_RF_ADDR_WIDTH-1:0]  fetch_rfb_adr_i,

  // from DECODE
  input [OPTION_RF_ADDR_WIDTH-1:0]  dcod_rfa_adr_i,
  input [OPTION_RF_ADDR_WIDTH-1:0]  dcod_rfb_adr_i,

  // from EXECUTE
  input                             exec_rf_wb_i,
  input [OPTION_RF_ADDR_WIDTH-1:0]  exec_rfd_adr_i,

  // from WB
  input                             wb_rf_wb_i,
  input [OPTION_RF_ADDR_WIDTH-1:0]  wb_rfd_adr_i,
  input [OPTION_OPERAND_WIDTH-1:0]  wb_result_i,

  // outputs
  output [OPTION_OPERAND_WIDTH-1:0] dcod_rfb_o,
  output [OPTION_OPERAND_WIDTH-1:0] exec_rfa_o,
  output [OPTION_OPERAND_WIDTH-1:0] exec_rfb_o
);

`include "mor1kx_utils.vh"

  localparam RF_ADDR_WIDTH = OPTION_RF_ADDR_WIDTH +
                            ((OPTION_RF_NUM_SHADOW_GPR == 1) ? 1 :
                             `clog2(OPTION_RF_NUM_SHADOW_GPR));

  //-----------//
  // FETCH->RF //
  //-----------//

  // ram blocks controls
  wire [OPTION_OPERAND_WIDTH-1:0]    rfa_dout;
  wire [OPTION_OPERAND_WIDTH-1:0]    rfb_dout;
  wire [RF_ADDR_WIDTH-1:0]           rfa_rdad;
  wire [RF_ADDR_WIDTH-1:0]           rfb_rdad;

  // WB address align
  wire [RF_ADDR_WIDTH-1:0] wb_rfd_adr_rf;

  // SPR/GPR access from bus signals
  wire [RF_ADDR_WIDTH-1:0] spr_bus_addr_rf = spr_bus_addr_i[RF_ADDR_WIDTH-1:0];
  wire spr_gpr_we, spr_gpr_re;

  // 1-clock strobe for GPR write
  //  - writting act could be blocked by exceptions processing
  //    because the istruction isn't completed and
  //    will be restarted by l.rfe
  wire wb_rf_we = wb_rf_wb_i & wb_new_result_i & (~pipeline_flush_i);

generate
// Zero-pad unused parts of vector
if (OPTION_RF_NUM_SHADOW_GPR > 0) begin : zero_pad_gen
  assign rfa_rdad[RF_ADDR_WIDTH-1:OPTION_RF_ADDR_WIDTH] =
         {(RF_ADDR_WIDTH-OPTION_RF_ADDR_WIDTH){1'b0}};
  assign rfb_rdad[RF_ADDR_WIDTH-1:OPTION_RF_ADDR_WIDTH] =
         {(RF_ADDR_WIDTH-OPTION_RF_ADDR_WIDTH){1'b0}};
  assign wb_rfd_adr_rf = {{(RF_ADDR_WIDTH-OPTION_RF_ADDR_WIDTH){1'b0}},wb_rfd_adr_i};
end
else begin
  assign wb_rfd_adr_rf = wb_rfd_adr_i;
end

// SPR/GPR access from bus
if ((FEATURE_DEBUGUNIT!="NONE") || (FEATURE_FASTCONTEXTS!="NONE") ||
    (OPTION_RF_NUM_SHADOW_GPR > 0)) begin : spr_gpr_controls_gen

  //  we don't expect R/W-collisions for SPRbus vs WB cycles since 
  //    SPRbus access start 1-clock later than WB (see logic in CTRL module)
  assign spr_gpr_we = (spr_bus_addr_i[15:9] == 7'h2) &
                      spr_bus_stb_i & spr_bus_we_i;

  assign spr_gpr_re = (spr_bus_addr_i[15:9] == 7'h2) &
                      spr_bus_stb_i & (~spr_bus_we_i);

  reg  spr_gpr_read_ack;
  always @(posedge clk)
    spr_gpr_read_ack <= spr_gpr_re;

  assign spr_gpr_ack_o = spr_gpr_we | (spr_gpr_re & spr_gpr_read_ack);

end
else begin

  assign spr_gpr_we    = 1'b0;
  assign spr_gpr_re    = 1'b0;
  assign spr_gpr_ack_o = 1'b1;

end
endgenerate

  // FETCH to DECODE hazards
  //  read/write hazard during FETCH->DECODE
  //  write value is bypassed for hazard cases
  wire fetch_wb2fetch_hazard_a =
    fetch_rf_adr_valid_i & wb_rf_we & (wb_rfd_adr_i == fetch_rfa_adr_i);
  wire fetch_wb2fetch_hazard_b =
    fetch_rf_adr_valid_i & wb_rf_we & (wb_rfd_adr_i == fetch_rfb_adr_i);

  // write signals
  wire                            rf_wren  = wb_rf_we | spr_gpr_we;
  wire [RF_ADDR_WIDTH-1:0]        rf_wradr = wb_rf_we ? wb_rfd_adr_rf : spr_bus_addr_rf;
  wire [OPTION_OPERAND_WIDTH-1:0] rf_wrdat = wb_rf_we ? wb_result_i   : spr_bus_dat_i;
  
  // read signals
  //  we handle R/W-collision for FETCH<->DECODE
  //  we don't expect R/W-collisions for SPRbus cycles since pipe is stalled till ACK
  assign rfa_rdad[OPTION_RF_ADDR_WIDTH-1:0] = fetch_rfa_adr_i;
  assign rfb_rdad[OPTION_RF_ADDR_WIDTH-1:0] = fetch_rfb_adr_i;
  wire   rfa_rden = fetch_rf_adr_valid_i & (~fetch_wb2fetch_hazard_a);
  wire   rfb_rden = fetch_rf_adr_valid_i & (~fetch_wb2fetch_hazard_b);

  // instance RF-A
  mor1kx_simple_dpram_sclk
  #(
    .ADDR_WIDTH      (RF_ADDR_WIDTH),
    .DATA_WIDTH      (OPTION_OPERAND_WIDTH),
    .CLEAR_ON_INIT   (OPTION_RF_CLEAR_ON_INIT),
    .ENABLE_BYPASS   (0)
  )
  rfa
  (
    .clk             (clk),
    .dout            (rfa_dout),
    .raddr           (rfa_rdad),
    .re              (rfa_rden),
    .waddr           (rf_wradr),
    .we              (rf_wren),
    .din             (rf_wrdat)
  );

  // instance RF-B
  mor1kx_simple_dpram_sclk
  #(
    .ADDR_WIDTH      (RF_ADDR_WIDTH),
    .DATA_WIDTH      (OPTION_OPERAND_WIDTH),
    .CLEAR_ON_INIT   (OPTION_RF_CLEAR_ON_INIT),
    .ENABLE_BYPASS   (0)
  )
  rfb
  (
    .clk             (clk),
    .dout            (rfb_dout),
    .raddr           (rfb_rdad),
    .re              (rfb_rden),
    .waddr           (rf_wradr),
    .we              (rf_wren),
    .din             (rf_wrdat)
  );


generate
if ((FEATURE_DEBUGUNIT!="NONE") || (FEATURE_FASTCONTEXTS!="NONE") ||
    (OPTION_RF_NUM_SHADOW_GPR > 0)) begin : rfspr_gen

  mor1kx_spram_en_w1st
  #(
     .ADDR_WIDTH      (RF_ADDR_WIDTH),
     .DATA_WIDTH      (OPTION_OPERAND_WIDTH),
     .CLEAR_ON_INIT   (OPTION_RF_CLEAR_ON_INIT)
  )
  rfspr
  (
    // clock
    .clk              (clk),
    // port
    .en               (rf_wren | spr_gpr_re), // enable port
    .we               (rf_wren),
    .addr             (rf_wradr), // == spr_bus_addr_rf for read
    .din              (rf_wrdat),
    .dout             (spr_gpr_dat_o)
  );

end
else begin

  assign spr_gpr_dat_o = {OPTION_OPERAND_WIDTH{1'b0}};

end
endgenerate

  // feed back from DECODE
  wire dcod_wb2dec_hazard_a;
  wire dcod_wb2dec_hazard_b;

  // Since the decode stage doesn't read from the register file, we have to
  // save any writes to the current read addresses in decode stage until
  // fetch latch in new values.
  // When fetch latch in the new values, and a writeback happens at the
  // same time, we bypass that value too.

  // 1-clock strobe to enable update bypass value register 
  // due to detected WB<->DECODE hazard
  wire wb2dec_hazard_we = wb_new_result_i & (~pipeline_flush_i);

  // Port A
  //  bypass RF-A cases
  wire fetch_bypass_a = fetch_wb2fetch_hazard_a |
                        // or bypass last WB-result
                        ((~fetch_rf_adr_valid_i) & wb2dec_hazard_we & dcod_wb2dec_hazard_a); 

  // for DECODE
  //  data for bypass on DECODE
  reg [OPTION_OPERAND_WIDTH-1:0] dcod_bypass_result_a;
  always @(posedge clk) begin
    if (fetch_bypass_a)
      dcod_bypass_result_a <= wb_result_i;
  end // @clock

  //  flag : "bypass on DECODE"
  reg dcod_bypass_a;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      dcod_bypass_a <= 1'b0;
    if (pipeline_flush_i)
      dcod_bypass_a <= 1'b0;
    else if (fetch_bypass_a)
      dcod_bypass_a <= 1'b1;
    else if (fetch_rf_adr_valid_i)
      dcod_bypass_a <= 1'b0;
  end // @clock

  // Port B
  //  bypass RF-B cases
  wire fetch_bypass_b = fetch_wb2fetch_hazard_b |
                        // or bypass last WB-result
                        ((~fetch_rf_adr_valid_i) & wb2dec_hazard_we & dcod_wb2dec_hazard_b);

  // for DECODE
  //  data for bypass on DECODE
  reg [OPTION_OPERAND_WIDTH-1:0] dcod_bypass_result_b;
  always @(posedge clk) begin
    if (fetch_bypass_b)
      dcod_bypass_result_b <= wb_result_i;
  end // @clock

  //  flag : "bypass on DECODE"
  reg dcod_bypass_b;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      dcod_bypass_b <= 1'b0;
    if (pipeline_flush_i)
      dcod_bypass_b <= 1'b0;
    else if (fetch_bypass_b)
      dcod_bypass_b <= 1'b1;
    else if (fetch_rf_adr_valid_i)
      dcod_bypass_b <= 1'b0;
  end // @clock


  //------------------------
  // DECODE stage (dcod_*)
  //------------------------

  // EXECUTE-to-DECODE hazard
  wire dcod_exe2dec_hazard_a = exec_rf_wb_i & (exec_rfd_adr_i == dcod_rfa_adr_i);
  wire dcod_exe2dec_hazard_b = exec_rf_wb_i & (exec_rfd_adr_i == dcod_rfb_adr_i);
  // to EXECUTE
  reg exec_exe2dec_hazard_a;
  reg exec_exe2dec_hazard_b;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      exec_exe2dec_hazard_a <= 1'b0;
      exec_exe2dec_hazard_b <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      exec_exe2dec_hazard_a <= 1'b0;
      exec_exe2dec_hazard_b <= 1'b0;
    end
    else if (padv_decode_i) begin
      exec_exe2dec_hazard_a <= dcod_exe2dec_hazard_a;
      exec_exe2dec_hazard_b <= dcod_exe2dec_hazard_b;
    end
  end // @clock


  //  WB-to-DECODE hazard
  assign dcod_wb2dec_hazard_a = wb_rf_wb_i & (wb_rfd_adr_i == dcod_rfa_adr_i);
  assign dcod_wb2dec_hazard_b = wb_rf_wb_i & (wb_rfd_adr_i == dcod_rfb_adr_i);


  // bypasses on DECODE
  wire [OPTION_OPERAND_WIDTH-1:0] dcod_rfa;
  wire [OPTION_OPERAND_WIDTH-1:0] dcod_rfb;

  assign dcod_rfa = dcod_wb2dec_hazard_a   ? wb_result_i :
                    dcod_bypass_a          ? dcod_bypass_result_a : // R/W collision for RF-A
                                             rfa_dout;

  assign dcod_rfb = dcod_wb2dec_hazard_b   ? wb_result_i :
                    dcod_bypass_b          ? dcod_bypass_result_b : // R/W collision for RF-B
                                             rfb_dout;
  // none latched output 
  assign dcod_rfb_o = dcod_rfb;
  // to EXECUTE
  reg [OPTION_OPERAND_WIDTH-1:0] exec_rfa;
  reg [OPTION_OPERAND_WIDTH-1:0] exec_rfb;
  always @(posedge clk) begin
    if (padv_decode_i) begin
       exec_rfa <= dcod_rfa;
       exec_rfb <= dcod_rfb;
    end
  end // @clock



  //--------------------------
  // EXECUTE stage (exec_*)
  //--------------------------

  // hazard resolving
  assign exec_rfa_o = exec_exe2dec_hazard_a ? wb_result_i :
                                              exec_rfa; // default: resolved on DECODE

  assign exec_rfb_o = exec_exe2dec_hazard_b ? wb_result_i :
                                              exec_rfb; // default: resolved on DECODE

endmodule // mor1kx_rf_marocchino
