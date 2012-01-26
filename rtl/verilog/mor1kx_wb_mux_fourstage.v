/*
 *
 * RF writeback mux 
 * 
 * Choose between ALU and LSU input.
 * 
 * All combinatorial
 * 
 */

`include "mor1kx-defines.v"

module mor1kx_wb_mux_fourstage
  (/*AUTOARG*/
   // Outputs
   rf_result_o,
   // Inputs
   clk, rst, alu_result_i, lsu_result_i, pc_execute_i, spr_i,
   op_jal_i, op_lsu_load_i, op_mfspr_i
   );

   parameter OPTION_OPERAND_WIDTH = 32;
   
   input clk, rst;

   input [OPTION_OPERAND_WIDTH-1:0] alu_result_i;
   input [OPTION_OPERAND_WIDTH-1:0] lsu_result_i;
   input [OPTION_OPERAND_WIDTH-1:0] pc_execute_i;
   input [OPTION_OPERAND_WIDTH-1:0] spr_i;

   output [OPTION_OPERAND_WIDTH-1:0] rf_result_o;   

   input 			      op_jal_i;
   input 			      op_lsu_load_i;
   input 			      op_mfspr_i;

  
   assign rf_result_o = op_lsu_load_i ? lsu_result_i :
			op_mfspr_i ? spr_i :
			/* TODO - maybe eliminate this adder */
			op_jal_i ? pc_execute_i + 8 :
			alu_result_i;

endmodule // mor1kx_wb_mux

   
		   
   
   
				     

  
