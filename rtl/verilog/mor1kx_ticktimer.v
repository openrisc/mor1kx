/* ****************************************************************************
 This Source Code Form is subject to the terms of the 
 Open Hardware Description License, v. 1.0. If a copy 
 of the OHDL was not distributed with this file, You 
 can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

 Description: mor1kx tick timer unit
 
 Copyright (C) 2012 Authors
 
 Author(s): Julius Baxter <juliusbaxter@gmail.com>
 
 ***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_ticktimer
  (/*AUTOARG*/
   // Outputs
   spr_ttmr_o, spr_ttcr_o, spr_bus_ack, spr_dat_o,
   // Inputs
   clk, rst, spr_we_i, spr_addr_i, spr_dat_i
   );

   input clk;
   input rst;

   output [31:0] spr_ttmr_o;
   output [31:0] spr_ttcr_o;

   // SPR Bus interface
   input 	 spr_we_i;
   input [15:0]  spr_addr_i;
   input [31:0]  spr_dat_i;
   output 	 spr_bus_ack;
   output [31:0] spr_dat_o;
   
   // Registers
   reg [31:0] 	 spr_ttmr;
   reg [31:0] 	 spr_ttcr;

   assign spr_ttmr_o = spr_ttmr;
   assign spr_ttcr_o = spr_ttcr;
   assign spr_bus_ack = spr_we_i;
   assign spr_dat_o = (spr_addr_i==`OR1K_SPR_TTCR_ADDR) ?
		      spr_ttcr :
		      (spr_addr_i==`OR1K_SPR_TTMR_ADDR) ?
		      spr_ttmr : 0;

   // Timer SPR control   
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_ttmr <= 0;
     else if (spr_we_i && spr_addr_i==`OR1K_SPR_TTMR_ADDR)
       spr_ttmr <= spr_dat_i[31:0];
     else if ((spr_ttmr[27:0]==spr_ttcr[27:0]) & spr_ttmr[29])
       spr_ttmr[28] <= 1; // Generate interrupt
   
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_ttcr <= 0;
     else if (spr_we_i && spr_addr_i==`OR1K_SPR_TTCR_ADDR)
       spr_ttcr <= spr_dat_i[31:0];
     else if (spr_ttmr[27:0]==spr_ttcr[27:0])
       begin
	  case(spr_ttmr[31:30])
	    2'b01: // Restart
	      spr_ttcr <= 0;
	    2'b11: // Continuous
	      spr_ttcr <= spr_ttcr + 1;
	    default: // Stop, or disabled
	      spr_ttcr <= spr_ttcr;
	  endcase // case (spr_ttmr[31:30])
       end // if (spr_ttmr[27:0]==spr_ttcr[27:0])
     else if (|spr_ttmr[31:30])
       spr_ttcr <= spr_ttcr + 1;

endmodule // mor1kx_ticktimer

