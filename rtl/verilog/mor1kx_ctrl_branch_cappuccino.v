/* ****************************************************************************
  This Source Code Form is subject to the terms of the
  Open Hardware Description License, v. 1.0. If a copy
  of the OHDL was not distributed with this file, You
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: mor1kx branch control

  jump/branch address and opcode input from execute stage

  flag input from control stage

  branch indication from control stage

  generate branch occurred and new address for fetch stage

  wholly combinatorial for now

  Copyright (C) 2012 Authors

   Author(s): Julius Baxter <juliusbaxter@gmail.com>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_ctrl_branch_cappuccino
  #(
    parameter OPTION_OPERAND_WIDTH = 32
    )
   (
    input 			      clk,
    input 			      rst,

    // Operand B from RF for l.jr/l.jalr
    input [OPTION_OPERAND_WIDTH-1:0]  ex_rfb_i,

    // Signals indicating jump/branch
    input 			      op_jr_i,

    // Inputs from decode stage
    input 			      decode_branch_i,
    input [OPTION_OPERAND_WIDTH-1:0]  decode_branch_target_i,

    input 			      padv_decode_i,
    input 			      decode_bubble_i,

    input 			      pipeline_flush_i,

    // Execute stage's instruction opcode in
    input [`OR1K_OPCODE_WIDTH-1:0]    execute_opc_insn_i,

    // Inputs from control unit - flag, branch indicator, dest PC
    input 			      ctrl_flag_i,

    input 			      ctrl_branch_exception_i,
    input [OPTION_OPERAND_WIDTH-1:0]  ctrl_branch_except_pc_i,

    input 			      execute_except_ibus_align_i,
    input 			      ctrl_except_ibus_align_i,

    input 			      ctrl_except_syscall_i,

    output 			      ctrl_branch_occur_o,
    output [OPTION_OPERAND_WIDTH-1:0] ctrl_branch_target_o
    );

   reg 				     ctrl_branch_occur_r;
   reg [OPTION_OPERAND_WIDTH-1:0]    ctrl_branch_target_r;

   wire 			     new_branch;
   wire [OPTION_OPERAND_WIDTH-1:0]    ctrl_branch_target;

   /* Here we move the branch detected in decode stage into execute stage,
    * to keep it inline with the other branches.
    * TODO: resolve those in decode stage already to avoid 1 cycle latency */
   reg imm_branch;
   always @(posedge clk `OR_ASYNC_RST)
     if (rst | pipeline_flush_i)
       imm_branch <= 0;
     else if (decode_bubble_i)
       imm_branch <= 0;
     else if (padv_decode_i)
       imm_branch <= decode_branch_i;

   reg [OPTION_OPERAND_WIDTH-1:0] imm_branch_target;
   always @(posedge clk)
     imm_branch_target <= decode_branch_target_i;

   // Exceptions take precedence
   assign ctrl_branch_occur_o = ctrl_branch_exception_i |
				/* we have to prevent branches when we have
				 * syscall exception in control stage
				 * TODO: check if there are other exceptions
				 * that need this too */
				!ctrl_except_syscall_i &
				(imm_branch |
				/* Only look at execute_except_ibus_align on the
				 * first cycle because potentially the branch
				 * target has changed one cycle later.
				 * TODO: share the registered branch target
				 * address between this module and execute ctrl
				 * module, which calculates if it's an alignment
				 * exception */
				(op_jr_i & !(execute_except_ibus_align_i &
					     !ctrl_branch_occur_r)));

   assign ctrl_branch_target_o = new_branch ? ctrl_branch_target :
				 ctrl_branch_target_r;

   assign ctrl_branch_target = ctrl_branch_exception_i ?
			       ctrl_branch_except_pc_i :
			       imm_branch ? imm_branch_target :
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
