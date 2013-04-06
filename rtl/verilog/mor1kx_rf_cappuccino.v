/* ****************************************************************************
  This Source Code Form is subject to the terms of the
  Open Hardware Description License, v. 1.0. If a copy
  of the OHDL was not distributed with this file, You
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: Register file for cappuccino pipeline

  Copyright (C) 2012 Authors

  Author(s): Julius Baxter <juliusbaxter@gmail.com>
             Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_rf_cappuccino
  #(
    parameter OPTION_RF_ADDR_WIDTH = 5,
    parameter OPTION_RF_WORDS = 32,

    parameter OPTION_OPERAND_WIDTH = 32
    )
   (
    input 			      clk,
    input 			      rst,

    // pipeline control signal in
    input 			      padv_execute_i,

    input 			      padv_decode_i,

    input 			      decode_valid_i,

    // GPR numbers
    input [OPTION_RF_ADDR_WIDTH-1:0]  decode_rfa_adr_i,
    input [OPTION_RF_ADDR_WIDTH-1:0]  decode_rfb_adr_i,

    input [OPTION_RF_ADDR_WIDTH-1:0]  execute_rfd_adr_i,
    input [OPTION_RF_ADDR_WIDTH-1:0]  ctrl_rfd_adr_i,
    input [OPTION_RF_ADDR_WIDTH-1:0]  wb_rfd_adr_i,

    // Write back signal indications
    input 			      execute_rf_wb_i,
    input 			      ctrl_rf_wb_i,
    input 			      wb_rf_wb_i,

    input [OPTION_OPERAND_WIDTH-1:0]  result_i,
    input [OPTION_OPERAND_WIDTH-1:0]  ctrl_alu_result_i,

    input 			      pipeline_flush_i,

    output [OPTION_OPERAND_WIDTH-1:0] execute_rfa_o,
    output [OPTION_OPERAND_WIDTH-1:0] execute_rfb_o
    );

   wire [OPTION_OPERAND_WIDTH-1:0]    rfa_ram_o;
   wire [OPTION_OPERAND_WIDTH-1:0]    rfb_ram_o;

   reg [OPTION_OPERAND_WIDTH-1:0]     wb_hazard_result;

   wire 			      rfa_rden;
   wire 			      rfb_rden;

   wire 			      rf_wren;

   reg 				      flushing;

   // Keep track of the flush signal, this is needed to not wrongly assert
   // execute_hazard after an exception (or rfe) has happened.
   // What happens in that case is that the instruction in execute stage is
   // invalid until the next padv_decode, so it's execute_rfd_adr can not be
   // used to evaluate the execute_hazard.
   always @(posedge clk)
     if (pipeline_flush_i)
       flushing <= 1;
     else if (padv_decode_i)
       flushing <= 0;

   // Detect hazards
   reg execute_hazard_a;
   reg execute_hazard_b;
   always @(posedge clk)
     if (pipeline_flush_i) begin
	execute_hazard_a <= 0;
	execute_hazard_b <= 0;
     end else if (padv_decode_i & !flushing) begin
	execute_hazard_a <= execute_rf_wb_i & (execute_rfd_adr_i == decode_rfa_adr_i);
	execute_hazard_b <= execute_rf_wb_i & (execute_rfd_adr_i == decode_rfb_adr_i);
     end

   reg [OPTION_OPERAND_WIDTH-1:0] execute_hazard_result_r;
   always @(posedge clk)
     if (decode_valid_i)
       execute_hazard_result_r <= ctrl_alu_result_i;

   wire [OPTION_OPERAND_WIDTH-1:0] execute_hazard_result;
   assign execute_hazard_result = decode_valid_i ? ctrl_alu_result_i :
				  execute_hazard_result_r;

   reg ctrl_hazard_a;
   reg ctrl_hazard_b;
   always @(posedge clk)
      if (padv_decode_i) begin
	 ctrl_hazard_a <= ctrl_rf_wb_i & (ctrl_rfd_adr_i == decode_rfa_adr_i);
	 ctrl_hazard_b <= ctrl_rf_wb_i & (ctrl_rfd_adr_i == decode_rfb_adr_i);
     end

   reg [OPTION_OPERAND_WIDTH-1:0] ctrl_hazard_result_r;
   always @(posedge clk)
     if (decode_valid_i)
       ctrl_hazard_result_r <= result_i;

   wire [OPTION_OPERAND_WIDTH-1:0] ctrl_hazard_result;
   assign ctrl_hazard_result = decode_valid_i ? result_i : ctrl_hazard_result_r;

   reg wb_hazard_a;
   reg wb_hazard_b;
   always @(posedge clk)
     if (padv_decode_i) begin
	wb_hazard_a <= wb_rf_wb_i & (wb_rfd_adr_i == decode_rfa_adr_i);
	wb_hazard_b <= wb_rf_wb_i & (wb_rfd_adr_i == decode_rfb_adr_i);
     end

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       wb_hazard_result <= 0;
     else if (padv_decode_i)
       wb_hazard_result <= result_i;

   assign execute_rfa_o = execute_hazard_a ? execute_hazard_result :
			  ctrl_hazard_a ? ctrl_hazard_result :
			  wb_hazard_a ? wb_hazard_result :
			  rfa_ram_o;

   assign execute_rfb_o = execute_hazard_b ? execute_hazard_result :
			  ctrl_hazard_b ? ctrl_hazard_result :
			  wb_hazard_b ? wb_hazard_result :
			  rfb_ram_o;


   assign rfa_rden = padv_decode_i;
   assign rfb_rden = padv_decode_i;
   assign rf_wren =  wb_rf_wb_i;

   mor1kx_rf_ram
     #(
       .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH),
       .OPTION_RF_ADDR_WIDTH(OPTION_RF_ADDR_WIDTH),
       .OPTION_RF_WORDS(OPTION_RF_WORDS)
       )
     rfa
     (
      .clk(clk),
      .rst(rst),
      .rdad_i(decode_rfa_adr_i),
      .rden_i(rfa_rden),
      .rdda_o(rfa_ram_o),
      .wrad_i(wb_rfd_adr_i),
      .wren_i(rf_wren),
      .wrda_i(result_i)
      );

   mor1kx_rf_ram
     #(
       .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH),
       .OPTION_RF_ADDR_WIDTH(OPTION_RF_ADDR_WIDTH),
       .OPTION_RF_WORDS(OPTION_RF_WORDS)
       )
   rfb
     (
      .clk(clk),
      .rst(rst),
      .rdad_i(decode_rfb_adr_i),
      .rden_i(rfb_rden),
      .rdda_o(rfb_ram_o),
      .wrad_i(wb_rfd_adr_i),
      .wren_i(rf_wren),
      .wrda_i(result_i)
      );

endmodule // mor1kx_rf_cappuccino
