/* ****************************************************************************
  This source describes Open Hardware and is licensed under the CERN-OHLW v2

  You may redistribute and modify this documentation and make products
  using it under the terms of the CERN-OHL-W v2 (https:/cern.ch/cern-ohl).
  This documentation is distributed WITHOUT ANY EXPRESS OR IMPLIED
  WARRANTY, INCLUDING OF MERCHANTABILITY, SATISFACTORY QUALITY
  AND FITNESS FOR A PARTICULAR PURPOSE. Please see the CERN-OHL-W v2
  for applicable conditions.

  Description: RF writeback mux for espresso pipeline

  Choose between ALU and LSU input. All combinatorial

  Copyright (C) 2012 Authors

  Author(s): Julius Baxter <juliusbaxter@gmail.com>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_wb_mux_espresso
  (/*AUTOARG*/
   // Outputs
   rf_result_o,
   // Inputs
   clk, rst, alu_result_i, lsu_result_i, ppc_i, pc_fetch_next_i,
   spr_i, op_jal_i, op_lsu_load_i, op_mfspr_i
   );

   parameter OPTION_OPERAND_WIDTH = 32;

   input clk, rst;

   input [OPTION_OPERAND_WIDTH-1:0] alu_result_i;
   input [OPTION_OPERAND_WIDTH-1:0] lsu_result_i;
   input [OPTION_OPERAND_WIDTH-1:0] ppc_i;
   input [OPTION_OPERAND_WIDTH-1:0] pc_fetch_next_i;
   input [OPTION_OPERAND_WIDTH-1:0] spr_i;

   output [OPTION_OPERAND_WIDTH-1:0] rf_result_o;

   input 			      op_jal_i;
   input 			      op_lsu_load_i;
   input 			      op_mfspr_i;


   assign rf_result_o = op_lsu_load_i ? lsu_result_i :
			op_mfspr_i ? spr_i :
			// Use the PC we've calcuated from the fetch unit
			// to save inferring a 32-bit adder here like we
			// would if we did "ppc_i + 8"
			op_jal_i ? pc_fetch_next_i:
			alu_result_i;

endmodule // mor1kx_wb_mux_espresso
