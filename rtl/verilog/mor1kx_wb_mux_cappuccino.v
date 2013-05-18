/* ****************************************************************************
  This Source Code Form is subject to the terms of the
  Open Hardware Description License, v. 1.0. If a copy
  of the OHDL was not distributed with this file, You
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: RF writeback mux

  Choose between ALU and LSU input.

  Copyright (C) 2012 Authors

  Author(s): Julius Baxter <juliusbaxter@gmail.com>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_wb_mux_cappuccino
  #(
    parameter OPTION_OPERAND_WIDTH = 32
    )
   (
    input 				  clk,
    input 				  rst,

    input [OPTION_OPERAND_WIDTH-1:0] 	  alu_result_i,
    input [OPTION_OPERAND_WIDTH-1:0] 	  lsu_result_i,
    input [OPTION_OPERAND_WIDTH-1:0] 	  spr_i,

    output reg [OPTION_OPERAND_WIDTH-1:0] rf_result_o,

    input 				  op_lsu_load_i,
    input 				  op_mfspr_i,
    input 				  lsu_valid_i
    );

   always @(posedge clk)
     if (op_mfspr_i)
       rf_result_o <= spr_i;
     else if (op_lsu_load_i)
       rf_result_o <= lsu_result_i;
     else
       rf_result_o <= alu_result_i;

endmodule // mor1kx_wb_mux_cappuccino
