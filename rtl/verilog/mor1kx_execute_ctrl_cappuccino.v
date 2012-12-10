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
  #(
    parameter OPTION_OPERAND_WIDTH = 32,
    parameter OPTION_RESET_PC = {{(OPTION_OPERAND_WIDTH-13){1'b0}},
				 `OR1K_RESET_VECTOR,8'd0},
    parameter OPTION_RF_ADDR_WIDTH = 5
    )
   (
    input 				  clk,
    input 				  rst,

    input 				  padv_i,
    input 				  padv_ctrl_i,

    // insn opcode, indicating what's going on
    input [`OR1K_OPCODE_WIDTH-1:0] 	  opc_insn_i,

    input 				  execute_except_ibus_err_i,
    input 				  execute_except_illegal_i,
    input 				  execute_except_syscall_i,
    input 				  lsu_except_dbus_i,
    input 				  lsu_except_align_i,
    input 				  execute_except_trap_i,

    input 				  pipeline_flush_i,

    input 				  op_alu_i,
    input 				  op_lsu_load_i,
    input 				  op_lsu_store_i,

    input 				  op_mfspr_i,
    input 				  alu_valid_i,
    input 				  lsu_valid_i,

    input 				  op_jr_i,
    input 				  op_jal_i,

    input [OPTION_OPERAND_WIDTH-1:0] 	  alu_result_i,
    input [OPTION_OPERAND_WIDTH-1:0] 	  adder_result_i,
    input [OPTION_OPERAND_WIDTH-1:0] 	  rfb_i,
    input 				  flag_set_i,
    input 				  flag_clear_i,
    input [OPTION_OPERAND_WIDTH-1:0] 	  pc_execute_i,

    input 				  exec_rf_wb_i,
    output 				  execute_rf_we_o,
    output reg 				  ctrl_rf_wb_o,
    output reg 				  wb_rf_wb_o,


    // address of destination register from execute stage
    input [OPTION_RF_ADDR_WIDTH-1:0] 	  exec_rfd_adr_i,
    output reg [OPTION_RF_ADDR_WIDTH-1:0] ctrl_rfd_adr_o,
    output reg [OPTION_RF_ADDR_WIDTH-1:0] wb_rfd_adr_o,

    input 				  exec_bubble_i,

    // Input from control stage for mfspr WE
    input 				  ctrl_mfspr_we_i,

    // Combinatorial output of instruction fetch align error
    output 				  execute_except_ibus_align_o,

    output reg [OPTION_OPERAND_WIDTH-1:0] ctrl_alu_result_o,
    output reg [OPTION_OPERAND_WIDTH-1:0] ctrl_lsu_adr_o,
    output reg [OPTION_OPERAND_WIDTH-1:0] ctrl_rfb_o,
    output reg 				  ctrl_flag_set_o,
    output reg 				  ctrl_flag_clear_o,
    output reg [OPTION_OPERAND_WIDTH-1:0] pc_ctrl_o,
    output reg [`OR1K_OPCODE_WIDTH-1:0]   ctrl_opc_insn_o,

    output reg 				  ctrl_op_lsu_load_o,
    output reg 				  ctrl_op_lsu_store_o,

    output reg 				  ctrl_op_mfspr_o,

    output reg 				  ctrl_op_jal_o,

    output reg 				  ctrl_except_ibus_err_o,
    output reg 				  ctrl_except_ibus_align_o,
    output reg 				  ctrl_except_illegal_o,
    output reg 				  ctrl_except_syscall_o,
    output reg 				  ctrl_except_dbus_o,
    output reg 				  ctrl_except_align_o,
    output reg 				  ctrl_except_trap_o,

    output reg 				  execute_waiting_o,

    output reg 				  execute_valid_o
    );

   wire 				  execute_valid;

   wire 				  op_mfspr;

   assign op_mfspr = opc_insn_i==`OR1K_OPCODE_MFSPR;

   // ALU or LSU stall execution, nothing else can
   assign execute_valid = (op_alu_i) ? alu_valid_i :
			  (op_lsu_load_i | op_lsu_store_i) ? lsu_valid_i :
			  1'b1;

   // Do writeback when we register our output to the next stage, or if
   // we're doing mfspr
   assign execute_rf_we_o = (exec_rf_wb_i & padv_i & !op_mfspr
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
     else begin
	if (padv_i) begin
	   ctrl_except_ibus_err_o <= execute_except_ibus_err_i;
	   ctrl_except_ibus_align_o <= execute_except_ibus_align_o;
	   ctrl_except_illegal_o <= execute_except_illegal_i;
	   ctrl_except_syscall_o <= execute_except_syscall_i;
	   ctrl_except_trap_o <= execute_except_trap_i;
	end
	ctrl_except_dbus_o <= lsu_except_dbus_i;
	ctrl_except_align_o <= lsu_except_align_i;
     end

   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	ctrl_alu_result_o <= 0;
	ctrl_lsu_adr_o <= 0;
     end else if (padv_i) begin
	if (op_lsu_load_i | op_lsu_store_i)
	  ctrl_lsu_adr_o <= adder_result_i;
	else
	  ctrl_alu_result_o <= alu_result_i;
     end

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
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

   // pc_ctrl should not advance when a nop bubble moves from execute to
   // ctrl/mem stage
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       pc_ctrl_o <= OPTION_RESET_PC;
     else if (padv_i & !exec_bubble_i)
       pc_ctrl_o <= pc_execute_i;

   wire op_rfe = ctrl_opc_insn_o==`OR1K_OPCODE_RFE;
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       ctrl_opc_insn_o <= `OR1K_OPCODE_NOP;
     else if (padv_ctrl_i & op_rfe)
       ctrl_opc_insn_o <= `OR1K_OPCODE_NOP;
     else if (padv_i)
       ctrl_opc_insn_o <= opc_insn_i;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	ctrl_op_mfspr_o <= 0;
	ctrl_op_jal_o <= 0;
    end else if (padv_i) begin
	ctrl_op_mfspr_o <= op_mfspr_i;
	ctrl_op_jal_o <= op_jal_i;
     end

   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	ctrl_op_lsu_load_o <= 0;
	ctrl_op_lsu_store_o <= 0;
     end else if (ctrl_except_align_o | ctrl_except_dbus_o) begin
	ctrl_op_lsu_load_o <= 0;
	ctrl_op_lsu_store_o <= 0;
    end else if (padv_i) begin
	ctrl_op_lsu_load_o <= op_lsu_load_i;
	ctrl_op_lsu_store_o <= op_lsu_store_i;
     end


   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	ctrl_rf_wb_o <= 0;
	ctrl_rfd_adr_o <= 0;
     end else if (padv_i) begin
	ctrl_rf_wb_o <= exec_rf_wb_i;
	ctrl_rfd_adr_o <= exec_rfd_adr_i;
     end

   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	wb_rf_wb_o <= 0;
	wb_rfd_adr_o <= 0;
     end else if (!ctrl_op_lsu_load_o | lsu_valid_i) begin
	wb_rf_wb_o <= ctrl_rf_wb_o & (padv_ctrl_i | lsu_valid_i);
	wb_rfd_adr_o <= ctrl_rfd_adr_o;
     end

endmodule // mor1kx_execute_ctrl_cappuccino
