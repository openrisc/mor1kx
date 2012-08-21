/* ****************************************************************************
  This Source Code Form is subject to the terms of the 
  Open Hardware Description License, v. 1.0. If a copy 
  of the OHDL was not distributed with this file, You 
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: Register file RAM
  
  Copyright (C) 2012 Authors
 
  Author(s): Julius Baxter <juliusbaxter@gmail.com>
 
***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_rf_ram
  (
   clk,
   rst,
   rdad_i,
   rden_i,
   rdda_o,
   wrad_i,
   wren_i,
   wrda_i
   );

   parameter OPTION_OPERAND_WIDTH = 32;
   parameter OPTION_RF_ADDR_WIDTH = 5;
   parameter OPTION_RF_WORDS = 32;
   
   input clk, rst;
   // Read ports
   input [OPTION_RF_ADDR_WIDTH-1:0] rdad_i;
   input 			   rden_i;
   output reg [OPTION_OPERAND_WIDTH-1:0] rdda_o;
   // Write ports
   input [OPTION_RF_ADDR_WIDTH-1:0] 	  wrad_i;
   input 				  wren_i;
   input [OPTION_OPERAND_WIDTH-1:0] 	  wrda_i;

   reg [OPTION_OPERAND_WIDTH-1:0] 	  ram [0:OPTION_RF_WORDS-1] /* synthesis syn_ramstyle = "no_rw_check" */;

   always @(posedge clk)
     if (rden_i)
       rdda_o <= ram[rdad_i];

   always @(posedge clk)
     if (wren_i)
       ram[wrad_i] <= wrda_i;

endmodule // mor1kx_rf_ram

   