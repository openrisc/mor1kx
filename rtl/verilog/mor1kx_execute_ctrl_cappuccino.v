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
    parameter OPTION_RF_ADDR_WIDTH = 5,
    parameter FEATURE_OVERFLOW = "NONE"
    )
   (
    input 				  clk,
    input 				  rst,

    input 				  padv_i,
    input 				  padv_ctrl_i,

    // insn opcode, indicating what's going on
    input [`OR1K_OPCODE_WIDTH-1:0] 	  opc_insn_i,

    input 				  execute_except_ibus_err_i,
    input 				  execute_except_itlb_miss_i,
    input 				  execute_except_ipagefault_i,
    input 				  execute_except_illegal_i,
    input 				  execute_except_ibus_align_i,
    input 				  execute_except_syscall_i,
    input 				  lsu_except_dbus_i,
    input 				  lsu_except_align_i,
    input 				  lsu_except_dtlb_miss_i,
    input 				  lsu_except_dpagefault_i,
    input 				  execute_except_trap_i,

    input 				  pipeline_flush_i,
    input 				  du_stall_i,

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
    input [OPTION_OPERAND_WIDTH-1:0] 	  execute_jal_result_i,
    input 				  flag_set_i,
    input 				  flag_clear_i,
    input 				  carry_set_i,
    input 				  carry_clear_i,
    input 				  overflow_set_i,
    input 				  overflow_clear_i,

    input [OPTION_OPERAND_WIDTH-1:0] 	  pc_execute_i,

    input 				  execute_rf_wb_i,
    output reg 				  ctrl_rf_wb_o,
    output reg 				  wb_rf_wb_o,


    // address of destination register from execute stage
    input [OPTION_RF_ADDR_WIDTH-1:0] 	  execute_rfd_adr_i,
    output reg [OPTION_RF_ADDR_WIDTH-1:0] ctrl_rfd_adr_o,
    output reg [OPTION_RF_ADDR_WIDTH-1:0] wb_rfd_adr_o,

    input 				  execute_bubble_i,

    // Input from control stage for mfspr WE
    input 				  ctrl_mfspr_we_i,

    output reg [OPTION_OPERAND_WIDTH-1:0] ctrl_alu_result_o,
    output reg [OPTION_OPERAND_WIDTH-1:0] ctrl_lsu_adr_o,
    output reg [OPTION_OPERAND_WIDTH-1:0] ctrl_rfb_o,
    output reg 				  ctrl_flag_set_o,
    output reg 				  ctrl_flag_clear_o,
    output reg 				  ctrl_carry_set_o,
    output reg 				  ctrl_carry_clear_o,
    output reg 				  ctrl_overflow_set_o,
    output reg 				  ctrl_overflow_clear_o,

    output reg [OPTION_OPERAND_WIDTH-1:0] pc_ctrl_o,
    output reg [`OR1K_OPCODE_WIDTH-1:0]   ctrl_opc_insn_o,

    output reg 				  ctrl_op_lsu_load_o,
    output reg 				  ctrl_op_lsu_store_o,

    output reg 				  ctrl_op_mfspr_o,

    output reg 				  ctrl_op_jal_o,

    output reg 				  ctrl_except_ibus_err_o,
    output reg 				  ctrl_except_itlb_miss_o,
    output reg 				  ctrl_except_ipagefault_o,
    output reg 				  ctrl_except_ibus_align_o,
    output reg 				  ctrl_except_illegal_o,
    output reg 				  ctrl_except_syscall_o,
    output reg 				  ctrl_except_dbus_o,
    output reg 				  ctrl_except_dtlb_miss_o,
    output reg 				  ctrl_except_dpagefault_o,
    output reg 				  ctrl_except_align_o,
    output reg 				  ctrl_except_trap_o,

    output reg 				  execute_waiting_o,

    output reg 				  execute_valid_o
    );

   wire 				  execute_valid;

   // ALU or LSU stall execution, nothing else can
   assign execute_valid = (ctrl_op_lsu_load_o | ctrl_op_lsu_store_o) ?
			  lsu_valid_i & (!op_alu_i | alu_valid_i) :
			  ctrl_op_mfspr_o ?
			  ctrl_mfspr_we_i & (!op_alu_i | alu_valid_i) :
			  op_alu_i ? alu_valid_i : 1'b1;

   always @*
     begin
	execute_valid_o = execute_valid;
	execute_waiting_o = !execute_valid;
     end

   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	ctrl_except_ibus_err_o <= 0;
	ctrl_except_itlb_miss_o <= 0;
	ctrl_except_ipagefault_o <= 0;
	ctrl_except_ibus_align_o <= 0;
	ctrl_except_illegal_o <= 0;
	ctrl_except_syscall_o <= 0;
	ctrl_except_trap_o <= 0;
	ctrl_except_dbus_o <= 0;
	ctrl_except_align_o <= 0;
     end
     else if (pipeline_flush_i & !du_stall_i) begin
	ctrl_except_ibus_err_o <= 0;
	ctrl_except_itlb_miss_o <= 0;
	ctrl_except_ipagefault_o <= 0;
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
	   ctrl_except_itlb_miss_o <= execute_except_itlb_miss_i;
	   ctrl_except_ipagefault_o <= execute_except_ipagefault_i;
	   ctrl_except_ibus_align_o <= execute_except_ibus_align_i;
	   ctrl_except_illegal_o <= execute_except_illegal_i;
	   ctrl_except_syscall_o <= execute_except_syscall_i;
	   ctrl_except_trap_o <= execute_except_trap_i;
	end
	ctrl_except_dbus_o <= lsu_except_dbus_i;
	ctrl_except_align_o <= lsu_except_align_i;
	ctrl_except_dtlb_miss_o <= lsu_except_dtlb_miss_i;
	ctrl_except_dpagefault_o <= lsu_except_dpagefault_i;
     end

   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	ctrl_alu_result_o <= 0;
	ctrl_lsu_adr_o <= 0;
     end else if (padv_i) begin
	if (op_lsu_load_i | op_lsu_store_i)
	  ctrl_lsu_adr_o <= adder_result_i;
	else if (op_jal_i)
	  ctrl_alu_result_o <= execute_jal_result_i;
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
	ctrl_carry_set_o <= 0;
	ctrl_carry_clear_o <= 0;
	ctrl_overflow_set_o <= 0;
	ctrl_overflow_clear_o <= 0;
     end
     else if (padv_i) begin
	ctrl_flag_set_o <= flag_set_i;
	ctrl_flag_clear_o <= flag_clear_i;
	ctrl_carry_set_o <= carry_set_i;
	ctrl_carry_clear_o <= carry_clear_i;
	if (FEATURE_OVERFLOW!="NONE") begin
	   ctrl_overflow_set_o <= overflow_set_i;
	   ctrl_overflow_clear_o <= overflow_clear_i;
	end
     end

   // pc_ctrl should not advance when a nop bubble moves from execute to
   // ctrl/mem stage
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       pc_ctrl_o <= OPTION_RESET_PC;
     else if (padv_i & !execute_bubble_i)
       pc_ctrl_o <= pc_execute_i;

   // The pipeline flush comes when the instruction that has caused
   // an exception or the instruction that has been interrupted is in
   // ctrl stage, so the padv_execute signal has to have higher prioity
   // than the pipeline flush in order to not accidently kill a valid
   // instruction coming in from execute stage.
   //
   // The tail of the pipeline should also not be flushed when the
   // pipeline_flush have been caused by a debug unit stall.

   wire op_rfe = ctrl_opc_insn_o==`OR1K_OPCODE_RFE;
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       ctrl_opc_insn_o <= `OR1K_OPCODE_NOP;
     else if (padv_ctrl_i & op_rfe)
       ctrl_opc_insn_o <= `OR1K_OPCODE_NOP;
     else if (padv_i)
       ctrl_opc_insn_o <= opc_insn_i;
     else if (pipeline_flush_i & !du_stall_i)
       ctrl_opc_insn_o <= `OR1K_OPCODE_NOP;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	ctrl_op_mfspr_o <= 0;
	ctrl_op_jal_o <= 0;
    end else if (padv_i) begin
	ctrl_op_mfspr_o <= op_mfspr_i;
	ctrl_op_jal_o <= op_jal_i;
    end else if (pipeline_flush_i & !du_stall_i) begin
	ctrl_op_mfspr_o <= 0;
	ctrl_op_jal_o <= 0;
    end

   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	ctrl_op_lsu_load_o <= 0;
	ctrl_op_lsu_store_o <= 0;
     end else if (ctrl_except_align_o | ctrl_except_dbus_o |
		  ctrl_except_dtlb_miss_o | ctrl_except_dpagefault_o) begin
	ctrl_op_lsu_load_o <= 0;
	ctrl_op_lsu_store_o <= 0;
    end else if (padv_i) begin
	ctrl_op_lsu_load_o <= op_lsu_load_i;
	ctrl_op_lsu_store_o <= op_lsu_store_i;
     end else if (pipeline_flush_i & !du_stall_i) begin
	ctrl_op_lsu_load_o <= 0;
	ctrl_op_lsu_store_o <= 0;
     end

   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	ctrl_rf_wb_o <= 0;
	ctrl_rfd_adr_o <= 0;
     end else if (padv_i) begin
	ctrl_rf_wb_o <= execute_rf_wb_i;
	ctrl_rfd_adr_o <= execute_rfd_adr_i;
     end else if (pipeline_flush_i & !du_stall_i) begin
	ctrl_rf_wb_o <= 0;
	ctrl_rfd_adr_o <= 0;
     end

   reg ctrl_mfspr_we_r;
   always @(posedge clk)
     ctrl_mfspr_we_r <= ctrl_mfspr_we_i;

   // load and mfpsr can stall from ctrl stage, so we have to hold off the
   // write back on them
   always @(posedge clk `OR_ASYNC_RST)
     if (rst | (pipeline_flush_i & !du_stall_i)) begin
	wb_rf_wb_o <= 0;
	wb_rfd_adr_o <= 0;
     end else if (ctrl_op_mfspr_o) begin
	wb_rf_wb_o <= ctrl_mfspr_we_i & (padv_ctrl_i | !ctrl_mfspr_we_r);
	wb_rfd_adr_o <= ctrl_rfd_adr_o;
     end else if (!ctrl_op_lsu_load_o | lsu_valid_i) begin
	wb_rf_wb_o <= ctrl_rf_wb_o & (padv_ctrl_i | lsu_valid_i);
	wb_rfd_adr_o <= ctrl_rfd_adr_o;
     end

endmodule // mor1kx_execute_ctrl_cappuccino
