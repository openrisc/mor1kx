/* ****************************************************************************
  This Source Code Form is subject to the terms of the 
  Open Hardware Description License, v. 1.0. If a copy 
  of the OHDL was not distributed with this file, You 
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: execute stage control
   
  Generate valid signal when stage is done
 
  Copyright (C) 2012 Authors
 
  Author(s): Julius Baxter <juliusbaxter@gmail.com>
 
***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_execute_ctrl_cappuccino
  (
   clk, rst,

   padv_i,

   // insn opcode, indicating what's going on
   opc_insn_i,
   // PC of execute stage instruction
   pc_execute_i,
   
   execute_except_ibus_err_i, execute_except_illegal_i, 
   execute_except_syscall_i, execute_except_trap_i,
   lsu_except_dbus_i, lsu_except_align_i,

   pipeline_flush_i,
   

   // Whether this operation relies on ALU output or not
   op_alu_i,
   
   op_lsu_load_i, op_lsu_store_i,   

   alu_valid_i, lsu_valid_i,

   op_jr_i,

   // Inputs that we'll want in control/SPR stage
   alu_result_i, rfb_i,
   flag_set_i, flag_clear_i,

   ctrl_mfspr_we_i,

   rf_wb_i,
   execute_rf_we_o,

   execute_except_ibus_align_o,

   ctrl_alu_result_o, ctrl_rfb_o,
   ctrl_flag_set_o, ctrl_flag_clear_o,
   pc_ctrl_o,
   ctrl_opc_insn_o,

   ctrl_except_ibus_err_o, ctrl_except_ibus_align_o, ctrl_except_illegal_o, 
   ctrl_except_syscall_o, ctrl_except_dbus_o, ctrl_except_align_o, 
   ctrl_except_trap_o,

   execute_waiting_o,
   
   execute_valid_o
   );

   parameter OPTION_OPERAND_WIDTH = 32;
   parameter OPTION_RESET_PC = {{(OPTION_OPERAND_WIDTH-13){1'b0}},
				`OR1K_RESET_VECTOR,8'd0};
   
   input clk, rst;
   
   input padv_i;

   // insn opcode, indicating what's going on
   input [`OR1K_OPCODE_WIDTH-1:0] opc_insn_i;
   
   input 			  execute_except_ibus_err_i,
				  execute_except_illegal_i, 
				  execute_except_syscall_i, lsu_except_dbus_i, 
				  lsu_except_align_i, execute_except_trap_i;

   input 			  pipeline_flush_i;

   input 			  op_alu_i;
   input 			  op_lsu_load_i;
   input 			  op_lsu_store_i;

   input 			  alu_valid_i, lsu_valid_i;

   input 			  op_jr_i;
   
   input [OPTION_OPERAND_WIDTH-1:0] alu_result_i;
   input [OPTION_OPERAND_WIDTH-1:0] rfb_i;
   input 			     flag_set_i, flag_clear_i;
   input [OPTION_OPERAND_WIDTH-1:0] pc_execute_i;

   input 			     rf_wb_i;
   
   // Input from control stage for mfspr WE
   input 			     ctrl_mfspr_we_i;
   
   
   output 			     execute_rf_we_o;

   // Combinatorial output of instruction fetch align error
   output 			     execute_except_ibus_align_o;
   
   output reg [OPTION_OPERAND_WIDTH-1:0] ctrl_alu_result_o;
   output reg [OPTION_OPERAND_WIDTH-1:0] ctrl_rfb_o;
   output reg 				  ctrl_flag_set_o, ctrl_flag_clear_o;
   output reg [OPTION_OPERAND_WIDTH-1:0] pc_ctrl_o;
   output reg [`OR1K_OPCODE_WIDTH-1:0] 	  ctrl_opc_insn_o;
   
   output reg 				  ctrl_except_ibus_err_o,
					  ctrl_except_ibus_align_o, 
					  ctrl_except_illegal_o, 
					  ctrl_except_syscall_o, 
					  ctrl_except_dbus_o, 
					  ctrl_except_align_o, 
					  ctrl_except_trap_o;

   output reg 				  execute_waiting_o;
   
   output reg 				  execute_valid_o;

   wire 				  execute_valid;

   wire 				  op_mfspr;

   assign op_mfspr = opc_insn_i==`OR1K_OPCODE_MFSPR;
   
   // ALU or LSU stall execution, nothing else can
   assign execute_valid = (op_alu_i) ? alu_valid_i :
			  (op_lsu_load_i | op_lsu_store_i) ? lsu_valid_i :
			  1'b1;

   // Do writeback when we register our output to the next stage, or if
   // we're doing mfspr
   assign execute_rf_we_o = (rf_wb_i & padv_i & !op_mfspr 
			     & !((op_lsu_load_i | op_lsu_store_i) &
				 lsu_except_dbus_i | lsu_except_align_i)) |
			    (op_mfspr & ctrl_mfspr_we_i);

   // Check for unaligned jump address from register
   assign execute_except_ibus_align_o = op_jr_i & (|rfb_i[1:0]);

   always @*
     begin
	execute_valid_o = execute_valid;
	execute_waiting_o = !execute_valid;
     end
   /*
  
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       execute_valid_o <= 0;
     else
       execute_valid_o <= execute_valid & padv_i & !execute_waiting_o;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       execute_waiting_o <= 0;
     else if (execute_valid)
       execute_waiting_o <= 0;
     else 
       execute_waiting_o <= (op_alu_i & !alu_valid_i) |
			    ((op_lsu_load_i | op_lsu_store_i) & 
			     !lsu_valid_i) & !padv_i;
    */
			 
   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	ctrl_except_ibus_err_o <= 0;
	ctrl_except_ibus_align_o <= 0;
	ctrl_except_illegal_o <= 0;
	ctrl_except_syscall_o <= 0;
	ctrl_except_trap_o <= 0;
	ctrl_except_dbus_o <= 0;
	ctrl_except_align_o <= 0;
     end
     else if (pipeline_flush_i) begin
	ctrl_except_ibus_err_o <= 0;
	ctrl_except_ibus_align_o <= 0;
	ctrl_except_illegal_o <= 0;
	ctrl_except_syscall_o <= 0;
	ctrl_except_trap_o <= 0;
	ctrl_except_dbus_o <= 0;
	ctrl_except_align_o <= 0;
     end
     else if (padv_i) begin
	ctrl_except_ibus_err_o <= execute_except_ibus_err_i;
	ctrl_except_ibus_align_o <= execute_except_ibus_align_o;
	ctrl_except_illegal_o <= execute_except_illegal_i;
	ctrl_except_syscall_o <= execute_except_syscall_i;
	ctrl_except_trap_o <= execute_except_trap_i;
	ctrl_except_dbus_o <= lsu_except_dbus_i;
	ctrl_except_align_o <= lsu_except_align_i;
     end

   // TODO - maybe replace these regs with routed copy from RF (last saved
   // result is same thing)
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
	ctrl_alu_result_o <= 0;
     else if (padv_i)
       ctrl_alu_result_o <= alu_result_i;
   
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       ctrl_rfb_o <= 0;
     else if (pipeline_flush_i)
       ctrl_rfb_o <= 0;
     else if (padv_i)
       ctrl_rfb_o <= rfb_i;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	ctrl_flag_set_o <= 0;
	ctrl_flag_clear_o <= 0;
     end
     else if (padv_i) begin
	ctrl_flag_set_o <= flag_set_i;
	ctrl_flag_clear_o <= flag_clear_i;
     end
   
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       pc_ctrl_o <= OPTION_RESET_PC;
     else if (padv_i)
       pc_ctrl_o <= pc_execute_i;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       ctrl_opc_insn_o <= `OR1K_OPCODE_NOP;
     else if (pipeline_flush_i)
       ctrl_opc_insn_o <= `OR1K_OPCODE_NOP;
     else if (padv_i)
       ctrl_opc_insn_o <= opc_insn_i;
   
endmodule // mor1kx_execute_ctrl_cappuccino


   
