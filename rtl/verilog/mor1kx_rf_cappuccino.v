/* ****************************************************************************
  This Source Code Form is subject to the terms of the 
  Open Hardware Description License, v. 1.0. If a copy 
  of the OHDL was not distributed with this file, You 
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: Register file for cappuccino pipeline
  
  Copyright (C) 2012 Authors
 
  Author(s): Julius Baxter <juliusbaxter@gmail.com>
 
***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_rf_cappuccino
  (
   clk, rst,

   // pipeline control signal in
   padv_execute_i,

   padv_decode_i,
   
   // GPR addresses from decode stage
   rfa_adr_i, rfb_adr_i, rfd_adr_i,
   
   // Writeback indication from decode stage
   rf_wb_i,
   // WE strobe from execute control stage
   execute_rf_we_i,

   
   // In from input MUX
   result_i,

   // Write mask
   write_mask_i,

   // RF operands out
   rfa_o, rfb_o
   
   );

   parameter OPTION_RF_ADDR_WIDTH = 5;
   parameter OPTION_RF_WORDS = 32;

   parameter OPTION_OPERAND_WIDTH = 32;
   
   input clk, rst;

   // pipeline control signal in
   input padv_execute_i;

   input padv_decode_i;

   // GPR numbers from decode stage
   input [OPTION_RF_ADDR_WIDTH-1:0]      rfd_adr_i;
   input [OPTION_RF_ADDR_WIDTH-1:0]      rfa_adr_i;
   input [OPTION_RF_ADDR_WIDTH-1:0]      rfb_adr_i;
   
   // Decode stage indicating writeback expected
   input 				rf_wb_i;
   // Execute stage asserting write back
   input 				execute_rf_we_i;
   
   input [OPTION_OPERAND_WIDTH-1:0]  result_i;
   
   input 			      write_mask_i;
   
   output [OPTION_OPERAND_WIDTH-1:0] rfa_o;
   output [OPTION_OPERAND_WIDTH-1:0] rfb_o;

   wire [OPTION_OPERAND_WIDTH-1:0]   rfa_o_mux;
   wire [OPTION_OPERAND_WIDTH-1:0]   rfb_o_mux;


   wire [OPTION_OPERAND_WIDTH-1:0]   rfa_ram_o;
   wire [OPTION_OPERAND_WIDTH-1:0]   rfb_ram_o;

   reg [OPTION_OPERAND_WIDTH-1:0]    result_last;
   reg [OPTION_RF_ADDR_WIDTH-1:0]      rfd_last;
   reg [OPTION_RF_ADDR_WIDTH-1:0]      rfd_r;
   reg [OPTION_RF_ADDR_WIDTH-1:0]      rfa_r;
   reg [OPTION_RF_ADDR_WIDTH-1:0]      rfb_r;
   
   wire 			      rfa_o_use_last;
   wire 			      rfb_o_use_last;
   reg 				      rfa_o_using_last;
   reg 				      rfb_o_using_last;

   reg 				      padv_decode_r;

   wire 			      no_wb_yet;
   reg 				      waiting_for_wb;

   wire 			      rfa_rden;
   wire 			      rfb_rden;
   
   wire 			      rf_wren;

   // Avoid read-write
   // Use when this instruction actually will write to its destination
   // register.
   assign rfa_o_use_last = (rfd_last == rfa_r); 
   assign rfb_o_use_last = (rfd_last == rfb_r);

   assign rfa_o = rfa_o_use_last ? result_last : rfa_ram_o;
   
   assign rfb_o = rfb_o_use_last ? result_last : rfb_ram_o;

   assign rfa_rden = padv_decode_i;
   assign rfb_rden = padv_decode_i;
   
   assign rf_wren = !write_mask_i & execute_rf_we_i;

   assign no_wb_yet = (waiting_for_wb | (padv_decode_r & rf_wb_i)) & !rf_wren;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	rfa_r <= 0;
	rfb_r <= 0;
	rfd_r <= 0;
     end
     else if (padv_decode_i)
       begin
	  rfa_r <= rfa_adr_i;
	  rfb_r <= rfb_adr_i;
	  rfd_r <= rfd_adr_i;
       end
   
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       rfd_last <= 0;
     else if (execute_rf_we_i & rf_wb_i)
       rfd_last <= rfd_r;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       result_last <= 0;
     else if (execute_rf_we_i & rf_wb_i)
       result_last <= result_i;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       padv_decode_r <= 0;
     else
       padv_decode_r <= padv_decode_i;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	rfa_o_using_last <= 0;
	rfb_o_using_last <= 0;
     end
     else begin
	if (!rfa_o_using_last)
	  rfa_o_using_last <= rfa_o_use_last & !rfa_rden;
	else if (rfa_rden)
	  rfa_o_using_last <= 0;

	if (!rfb_o_using_last)
	  rfb_o_using_last <= rfb_o_use_last & !rfb_rden;
	else if (rfb_rden)
	  rfb_o_using_last <= 0;
     end

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
	waiting_for_wb <= 0;
     else if (execute_rf_we_i)
       waiting_for_wb <= 0;
     else if (!waiting_for_wb & padv_decode_r & rf_wb_i)
       waiting_for_wb <= 1;
	
   
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
      .rdad_i(rfa_adr_i),
      .rden_i(rfa_rden),
      .rdda_o(rfa_ram_o),
      .wrad_i(rfd_r),
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
      .rdad_i(rfb_adr_i),
      .rden_i(rfb_rden),
      .rdda_o(rfb_ram_o),
      .wrad_i(rfd_r),
      .wren_i(rf_wren),
      .wrda_i(result_i)
      );

endmodule // mor1kx_rf_cappuccino

