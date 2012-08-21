/* ****************************************************************************
  This Source Code Form is subject to the terms of the 
  Open Hardware Description License, v. 1.0. If a copy 
  of the OHDL was not distributed with this file, You 
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: mor1k branch control

  jump/branch address and opcode input from execute stage
  
  flag input from control stage
  
  branch indication from control stage
  
  generate branch occurred and new address for fetch stage
  
  wholly combinatorial for now
  
  Copyright (C) 2012 Authors
 
  Author(s): Julius Baxter <juliusbaxter@gmail.com>
 
***************************************************************************** */

/*
 *
 * 
 */

`include "mor1kx-defines.v"

module mor1kx_ctrl_branch_cappuccino
  (
   clk, rst,
   
   // ALU result from execute stage - target of l.bf/l.bnf/l.j/l.jal
   ex_alu_result_i,
   // Operand B from RF for l.jr/l.jalr
   ex_rfb_i,

   // Signals indicating jump/branch
   op_jbr_i,
   op_jr_i,

   // Execute stage's instruction opcode in   
   execute_opc_insn_i,

   // Inputs from control unit - flag, branch indicator, dest PC
   ctrl_flag_i,
   ctrl_branch_exception_i,
   ctrl_branch_except_pc_i,

   // Input from execute_ctrl stage, indicating of branch from register
   // is unaligned
   execute_except_ibus_align_i,
   ctrl_except_ibus_align_i,

   ctrl_branch_occur_o,
   ctrl_branch_target_o
   );

   parameter OPTION_OPERAND_WIDTH = 32;
   
   input clk, rst;
   
   // ALU result from execute stage - target of l.bf/l.bnf/l.j/l.jal
   input [OPTION_OPERAND_WIDTH-1:0] ex_alu_result_i;
   
   // Operand B from RF for l.jr/l.jalr
   input [OPTION_OPERAND_WIDTH-1:0] ex_rfb_i;

   // Signals indicating jump/branch
   input 			     op_jbr_i, op_jr_i;
 
   // Execute stage's instruction opcode in   
   input [`OR1K_OPCODE_WIDTH-1:0]    execute_opc_insn_i;

   // Inputs from control unit - flag, branch indicator, dest PC
   input 			     ctrl_flag_i;
   
   input 			     ctrl_branch_exception_i;
   input [OPTION_OPERAND_WIDTH-1:0] ctrl_branch_except_pc_i;

   input 			     execute_except_ibus_align_i;
   input 			     ctrl_except_ibus_align_i;

   output 			     ctrl_branch_occur_o;
   output [OPTION_OPERAND_WIDTH-1:0] ctrl_branch_target_o;

   reg 				     ctrl_branch_occur_r;
   reg [OPTION_OPERAND_WIDTH-1:0]    ctrl_branch_target_r;

   wire 			     new_branch;
   wire [OPTION_OPERAND_WIDTH-1:0]    ctrl_branch_target;

   // Exceptions take precedence
   assign ctrl_branch_occur_o = (ctrl_branch_exception_i) |
				// instruction is branch, and flag is right
				(op_jbr_i &
				 // is l.j or l.jal
				 (!(|execute_opc_insn_i[2:1]) |
				  // is l.bf/bnf and flag is right
				  (execute_opc_insn_i[2]==ctrl_flag_i))) |
				/* Only look at execute_except_ibus_align on the first cycle because potentially the branch target has changed one cycle later. TODO: share the registered branch target address between this module and execute ctrl module, which calculates if it's an alignment exception */
				(op_jr_i & !(execute_except_ibus_align_i & !ctrl_branch_occur_r));

   assign ctrl_branch_target_o = new_branch ? ctrl_branch_target :
				 ctrl_branch_target_r;
   
   assign ctrl_branch_target = ctrl_branch_exception_i ? 
				 ctrl_branch_except_pc_i :
				 op_jbr_i ? ex_alu_result_i :
				 ex_rfb_i;

   always @(posedge clk)
     if (rst)
       ctrl_branch_occur_r <= 0;
     else
       ctrl_branch_occur_r <= ctrl_branch_occur_o;

   // detect rising edge on branch_occur signal
   assign new_branch = !ctrl_branch_occur_r & ctrl_branch_occur_o;

   /* Have to register the branch target on each new branch because of the
    case where we have a sequence like l.lwz rX, 0(rX); l.jalr rX and the
    target address is only present for a cycle. Another possibility is to
    detect this case in the control logic and tell the RF to hold that 
    particular output value until the fetch stage has registered it instead
    of having _another_ 32-bit register here*/
   always @(posedge clk)
     if (rst)
       ctrl_branch_target_r <= 0;
     else if (new_branch)
       ctrl_branch_target_r <= ctrl_branch_target;
   
   
   
endmodule // mor1kx_ctrl_branch_cappuccino

