/* ****************************************************************************
  This Source Code Form is subject to the terms of the 
  Open Hardware Description License, v. 1.0. If a copy 
  of the OHDL was not distributed with this file, You 
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: "Cappuccino" pipeline CPU module
  
  Copyright (C) 2012 Authors
 
  Author(s): Julius Baxter <juliusbaxter@gmail.com>
 
***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_cpu_cappuccino
  (/*AUTOARG*/
   // Outputs
   ibus_adr_o, ibus_req_o, dbus_adr_o, dbus_dat_o, dbus_req_o,
   dbus_bsel_o, dbus_we_o, du_dat_o, du_ack_o, du_stall_o,
   spr_bus_addr_o, spr_bus_we_o, spr_bus_stb_o, spr_bus_dat_o,
   spr_sr_o,
   // Inputs
   clk, rst, ibus_err_i, ibus_ack_i, ibus_dat_i, dbus_err_i,
   dbus_ack_i, dbus_dat_i, irq_i, du_addr_i, du_stb_i, du_dat_i,
   du_we_i, du_stall_i, spr_bus_dat_dc_i, spr_bus_ack_dc_i,
   spr_bus_dat_dmmu_i, spr_bus_ack_dmmu_i, spr_bus_dat_immu_i,
   spr_bus_ack_immu_i, spr_bus_dat_mac_i, spr_bus_ack_mac_i,
   spr_bus_dat_pmu_i, spr_bus_ack_pmu_i, spr_bus_dat_pcu_i,
   spr_bus_ack_pcu_i, spr_bus_dat_fpu_i, spr_bus_ack_fpu_i
   );

   input clk, rst;

   parameter OPTION_OPERAND_WIDTH = 32;
   
   parameter FEATURE_DATACACHE = "NONE";
   parameter OPTION_DCACHE_BLOCK_WIDTH = 5;
   parameter OPTION_DCACHE_SET_WIDTH = 9;
   parameter OPTION_DCACHE_WAYS = 2;
   parameter FEATURE_DMMU = "NONE";
   parameter FEATURE_INSTRUCTIONCACHE = "NONE";
   parameter OPTION_ICACHE_BLOCK_WIDTH = 5;
   parameter OPTION_ICACHE_SET_WIDTH = 9;
   parameter OPTION_ICACHE_WAYS = 2;
   parameter OPTION_ICACHE_LIMIT_WIDTH = 32;
   parameter FEATURE_IMMU = "NONE";
   parameter FEATURE_PIC = "ENABLED";
   parameter FEATURE_TIMER = "ENABLED";
   parameter FEATURE_DEBUGUNIT = "NONE";
   parameter FEATURE_PERFCOUNTERS = "NONE";
   parameter FEATURE_MAC = "NONE";

   parameter FEATURE_SYSCALL = "ENABLED";
   parameter FEATURE_TRAP = "ENABLED";
   parameter FEATURE_RANGE = "ENABLED";

   parameter OPTION_PIC_TRIGGER = "EDGE";

   parameter FEATURE_DSX		= "NONE";
   parameter FEATURE_FASTCONTEXTS	= "NONE";
   parameter FEATURE_OVERFLOW		= "NONE";

   parameter OPTION_RF_ADDR_WIDTH = 5;
   parameter OPTION_RF_WORDS = 32;

   parameter OPTION_RESET_PC = {{(OPTION_OPERAND_WIDTH-13){1'b0}},
				`OR1K_RESET_VECTOR,8'd0};

   parameter FEATURE_MULTIPLIER = "THREESTAGE";
   parameter FEATURE_DIVIDER = "NONE";

   parameter FEATURE_ADDC = "NONE";
   parameter FEATURE_SRA = "ENABLED";
   parameter FEATURE_ROR = "NONE";
   parameter FEATURE_EXT = "NONE";
   parameter FEATURE_CMOV = "NONE";
   parameter FEATURE_FFL1 = "NONE";
   
   parameter FEATURE_CUST1 = "NONE";
   parameter FEATURE_CUST2 = "NONE";
   parameter FEATURE_CUST3 = "NONE";
   parameter FEATURE_CUST4 = "NONE";
   parameter FEATURE_CUST5 = "NONE";
   parameter FEATURE_CUST6 = "NONE";
   parameter FEATURE_CUST7 = "NONE";
   parameter FEATURE_CUST8 = "NONE";
   
   parameter OPTION_SHIFTER = "ENABLED";
   
   // Instruction bus
   input ibus_err_i;
   input ibus_ack_i;
   input [`OR1K_INSN_WIDTH-1:0] ibus_dat_i;
   output [OPTION_OPERAND_WIDTH-1:0] ibus_adr_o;
   output 			     ibus_req_o;

   // Data bus
   input 			     dbus_err_i;
   input 			     dbus_ack_i;
   input [OPTION_OPERAND_WIDTH-1:0]  dbus_dat_i;
   output [OPTION_OPERAND_WIDTH-1:0] dbus_adr_o;
   output [OPTION_OPERAND_WIDTH-1:0] dbus_dat_o;
   output 			     dbus_req_o;
   output [3:0] 		     dbus_bsel_o;
   output 			     dbus_we_o;
   
   // Interrupts
   input [31:0] 		     irq_i;
   
   // Debug interface
   input [15:0] 		     du_addr_i;
   input 			     du_stb_i;
   input [OPTION_OPERAND_WIDTH-1:0]  du_dat_i;
   input 			     du_we_i;
   output [OPTION_OPERAND_WIDTH-1:0] du_dat_o;
   output 			     du_ack_o;
   // Stall control from debug interface
   input 			     du_stall_i;
   output 			     du_stall_o;

   // SPR accesses to external units (cache, mmu, etc.)
   output [15:0] 		     spr_bus_addr_o;
   output 			     spr_bus_we_o;
   output 			     spr_bus_stb_o;
   output [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o;
   input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_dc_i;
   input 			     spr_bus_ack_dc_i;   
//SJK   input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_ic_i;
//SJK   input 			     spr_bus_ack_ic_i;   
   input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_dmmu_i;
   input 			     spr_bus_ack_dmmu_i;   
   input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_immu_i;
   input 			     spr_bus_ack_immu_i;   
   input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_mac_i;
   input 			     spr_bus_ack_mac_i;   
   input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_pmu_i;
   input 			     spr_bus_ack_pmu_i;   
   input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_pcu_i;
   input 			     spr_bus_ack_pcu_i;   
   input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_fpu_i;
   input 			     spr_bus_ack_fpu_i;   
   output [15:0] 		     spr_sr_o;

   wire [OPTION_OPERAND_WIDTH-1:0]   pc_fetch_to_decode;
   wire [`OR1K_INSN_WIDTH-1:0] 	     insn_fetch_to_decode;
   wire [OPTION_OPERAND_WIDTH-1:0]   pc_decode_to_execute;
   wire [OPTION_OPERAND_WIDTH-1:0]   pc_execute_to_ctrl;
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [OPTION_OPERAND_WIDTH-1:0] alu_result_o;// From mor1kx_execute_alu of mor1kx_execute_alu.v
   wire			alu_valid_o;		// From mor1kx_execute_alu of mor1kx_execute_alu.v
   wire [OPTION_OPERAND_WIDTH-1:0] ctrl_alu_result_o;// From mor1kx_execute_ctrl_cappuccino of mor1kx_execute_ctrl_cappuccino.v
   wire [OPTION_OPERAND_WIDTH-1:0] ctrl_branch_except_pc_o;// From mor1kx_ctrl_cappuccino of mor1kx_ctrl_cappuccino.v
   wire			ctrl_branch_exception_o;// From mor1kx_ctrl_cappuccino of mor1kx_ctrl_cappuccino.v
   wire			ctrl_branch_occur_o;	// From mor1kx_ctrl_branch_cappuccino of mor1kx_ctrl_branch_cappuccino.v
   wire [OPTION_OPERAND_WIDTH-1:0] ctrl_branch_target_o;// From mor1kx_ctrl_branch_cappuccino of mor1kx_ctrl_branch_cappuccino.v
   wire			ctrl_except_align_o;	// From mor1kx_execute_ctrl_cappuccino of mor1kx_execute_ctrl_cappuccino.v
   wire			ctrl_except_dbus_o;	// From mor1kx_execute_ctrl_cappuccino of mor1kx_execute_ctrl_cappuccino.v
   wire			ctrl_except_ibus_align_o;// From mor1kx_execute_ctrl_cappuccino of mor1kx_execute_ctrl_cappuccino.v
   wire			ctrl_except_ibus_err_o;	// From mor1kx_execute_ctrl_cappuccino of mor1kx_execute_ctrl_cappuccino.v
   wire			ctrl_except_illegal_o;	// From mor1kx_execute_ctrl_cappuccino of mor1kx_execute_ctrl_cappuccino.v
   wire			ctrl_except_syscall_o;	// From mor1kx_execute_ctrl_cappuccino of mor1kx_execute_ctrl_cappuccino.v
   wire			ctrl_except_trap_o;	// From mor1kx_execute_ctrl_cappuccino of mor1kx_execute_ctrl_cappuccino.v
   wire			ctrl_flag_clear_o;	// From mor1kx_execute_ctrl_cappuccino of mor1kx_execute_ctrl_cappuccino.v
   wire			ctrl_flag_o;		// From mor1kx_ctrl_cappuccino of mor1kx_ctrl_cappuccino.v
   wire			ctrl_flag_set_o;	// From mor1kx_execute_ctrl_cappuccino of mor1kx_execute_ctrl_cappuccino.v
   wire			ctrl_mfspr_we_o;	// From mor1kx_ctrl_cappuccino of mor1kx_ctrl_cappuccino.v
   wire [`OR1K_OPCODE_WIDTH-1:0] ctrl_opc_insn_o;// From mor1kx_execute_ctrl_cappuccino of mor1kx_execute_ctrl_cappuccino.v
   wire [OPTION_OPERAND_WIDTH-1:0] ctrl_rfb_o;	// From mor1kx_execute_ctrl_cappuccino of mor1kx_execute_ctrl_cappuccino.v
   wire			decode_except_ibus_err_o;// From mor1kx_fetch_cappuccino of mor1kx_fetch_cappuccino.v
   wire			decode_valid_o;		// From mor1kx_decode of mor1kx_decode.v
   wire			du_restart_o;		// From mor1kx_ctrl_cappuccino of mor1kx_ctrl_cappuccino.v
   wire [OPTION_OPERAND_WIDTH-1:0] du_restart_pc_o;// From mor1kx_ctrl_cappuccino of mor1kx_ctrl_cappuccino.v
   wire			execute_except_ibus_align_o;// From mor1kx_execute_ctrl_cappuccino of mor1kx_execute_ctrl_cappuccino.v
   wire			execute_except_ibus_err_o;// From mor1kx_decode of mor1kx_decode.v
   wire			execute_except_illegal_o;// From mor1kx_decode of mor1kx_decode.v
   wire			execute_except_syscall_o;// From mor1kx_decode of mor1kx_decode.v
   wire			execute_except_trap_o;	// From mor1kx_decode of mor1kx_decode.v
   wire			execute_rf_we_o;	// From mor1kx_execute_ctrl_cappuccino of mor1kx_execute_ctrl_cappuccino.v
   wire			execute_valid_o;	// From mor1kx_execute_ctrl_cappuccino of mor1kx_execute_ctrl_cappuccino.v
   wire			execute_waiting_o;	// From mor1kx_execute_ctrl_cappuccino of mor1kx_execute_ctrl_cappuccino.v
   wire			fetch_branch_taken_o;	// From mor1kx_fetch_cappuccino of mor1kx_fetch_cappuccino.v
   wire			fetch_valid_o;		// From mor1kx_fetch_cappuccino of mor1kx_fetch_cappuccino.v
   wire			flag_clear_o;		// From mor1kx_execute_alu of mor1kx_execute_alu.v
   wire			flag_set_o;		// From mor1kx_execute_alu of mor1kx_execute_alu.v
   wire			ic_ack_o;		// From mor1kx_icache of mor1kx_icache.v
   wire [OPTION_OPERAND_WIDTH-1:0] ic_dat_o;	// From mor1kx_icache of mor1kx_icache.v
   wire			ic_err_o;		// From mor1kx_icache of mor1kx_icache.v
   wire [`OR1K_IMM_WIDTH-1:0] imm16_o;		// From mor1kx_decode of mor1kx_decode.v
   wire [9:0]		immjbr_upper_o;		// From mor1kx_decode of mor1kx_decode.v
   wire			lsu_except_align_o;	// From mor1kx_lsu_cappuccino of mor1kx_lsu_cappuccino.v
   wire			lsu_except_dbus_o;	// From mor1kx_lsu_cappuccino of mor1kx_lsu_cappuccino.v
   wire [OPTION_OPERAND_WIDTH-1:0] lsu_result_o;// From mor1kx_lsu_cappuccino of mor1kx_lsu_cappuccino.v
   wire			lsu_valid_o;		// From mor1kx_lsu_cappuccino of mor1kx_lsu_cappuccino.v
   wire [OPTION_OPERAND_WIDTH-1:0] mfspr_dat_o;	// From mor1kx_ctrl_cappuccino of mor1kx_ctrl_cappuccino.v
   wire			op_alu_o;		// From mor1kx_decode of mor1kx_decode.v
   wire			op_jal_o;		// From mor1kx_decode of mor1kx_decode.v
   wire			op_jbr_o;		// From mor1kx_decode of mor1kx_decode.v
   wire			op_jr_o;		// From mor1kx_decode of mor1kx_decode.v
   wire			op_lsu_load_o;		// From mor1kx_decode of mor1kx_decode.v
   wire			op_lsu_store_o;		// From mor1kx_decode of mor1kx_decode.v
   wire			op_mfspr_o;		// From mor1kx_decode of mor1kx_decode.v
   wire [`OR1K_ALU_OPC_WIDTH-1:0] opc_alu_o;	// From mor1kx_decode of mor1kx_decode.v
   wire [`OR1K_ALU_OPC_WIDTH-1:0] opc_alu_secondary_o;// From mor1kx_decode of mor1kx_decode.v
   wire [`OR1K_OPCODE_WIDTH-1:0] opc_insn_o;	// From mor1kx_decode of mor1kx_decode.v
   wire			padv_decode_o;		// From mor1kx_ctrl_cappuccino of mor1kx_ctrl_cappuccino.v
   wire			padv_execute_o;		// From mor1kx_ctrl_cappuccino of mor1kx_ctrl_cappuccino.v
   wire			padv_fetch_o;		// From mor1kx_ctrl_cappuccino of mor1kx_ctrl_cappuccino.v
   wire [OPTION_OPERAND_WIDTH-1:0] pc_addr_o;	// From mor1kx_fetch_cappuccino of mor1kx_fetch_cappuccino.v
   wire [OPTION_OPERAND_WIDTH-1:0] pc_fetch_o;	// From mor1kx_fetch_cappuccino of mor1kx_fetch_cappuccino.v
   wire			pipeline_flush_o;	// From mor1kx_ctrl_cappuccino of mor1kx_ctrl_cappuccino.v
   wire [OPTION_OPERAND_WIDTH-1:0] rf_result_o;	// From mor1kx_wb_mux_cappuccino of mor1kx_wb_mux_cappuccino.v
   wire			rf_wb_o;		// From mor1kx_decode of mor1kx_decode.v
   wire [OPTION_RF_ADDR_WIDTH-1:0] rfa_adr_o;	// From mor1kx_decode of mor1kx_decode.v
   wire [OPTION_OPERAND_WIDTH-1:0] rfa_o;	// From mor1kx_rf_cappuccino of mor1kx_rf_cappuccino.v
   wire [OPTION_RF_ADDR_WIDTH-1:0] rfb_adr_o;	// From mor1kx_decode of mor1kx_decode.v
   wire [OPTION_OPERAND_WIDTH-1:0] rfb_o;	// From mor1kx_rf_cappuccino of mor1kx_rf_cappuccino.v
   wire [OPTION_RF_ADDR_WIDTH-1:0] rfd_adr_o;	// From mor1kx_decode of mor1kx_decode.v
   wire			spr_bus_ack_ic_i;	// From mor1kx_icache of mor1kx_icache.v
   wire [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_ic_i;// From mor1kx_icache of mor1kx_icache.v
   // End of automatics

   /* mor1kx_fetch_cappuccino AUTO_TEMPLATE (
    .padv_i				(padv_fetch_o),
    .branch_occur_i			(ctrl_branch_occur_o),
    .branch_dest_i			(ctrl_branch_target_o),
    .pipeline_flush_i			(pipeline_flush_o),
    .pc_decode_o			(pc_fetch_to_decode),
    .decode_insn_o			(insn_fetch_to_decode),
    .du_restart_pc_i			(du_restart_pc_o),
    .du_restart_i			(du_restart_o),
    .ibus_err_i				(ic_err_o),
    .ibus_ack_i				(ic_ack_o),
    .ibus_dat_i				(ic_dat_o),
    ); */
   mor1kx_fetch_cappuccino
     #(
       .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH),
       .OPTION_RESET_PC(OPTION_RESET_PC)
       )
     mor1kx_fetch_cappuccino
     (/*AUTOINST*/
      // Outputs
      .pc_decode_o			(pc_fetch_to_decode),	 // Templated
      .decode_insn_o			(insn_fetch_to_decode),	 // Templated
      .fetch_valid_o			(fetch_valid_o),
      .pc_addr_o			(pc_addr_o[OPTION_OPERAND_WIDTH-1:0]),
      .pc_fetch_o			(pc_fetch_o[OPTION_OPERAND_WIDTH-1:0]),
      .decode_except_ibus_err_o		(decode_except_ibus_err_o),
      .fetch_branch_taken_o		(fetch_branch_taken_o),
      // Inputs
      .clk				(clk),
      .rst				(rst),
      .ibus_err_i			(ic_err_o),		 // Templated
      .ibus_ack_i			(ic_ack_o),		 // Templated
      .ibus_dat_i			(ic_dat_o),		 // Templated
      .padv_i				(padv_fetch_o),		 // Templated
      .branch_occur_i			(ctrl_branch_occur_o),	 // Templated
      .branch_dest_i			(ctrl_branch_target_o),	 // Templated
      .du_restart_pc_i			(du_restart_pc_o),	 // Templated
      .du_restart_i			(du_restart_o),		 // Templated
      .pipeline_flush_i			(pipeline_flush_o));	 // Templated

   /* mor1kx_icache AUTO_TEMPLATE (
    // Outputs
    .cpu_err_o			(ic_err_o),
    .cpu_ack_o			(ic_ack_o),
    .cpu_dat_o			(ic_dat_o[OPTION_OPERAND_WIDTH-1:0]),
    .spr_bus_dat_o		(spr_bus_dat_ic_i[OPTION_OPERAND_WIDTH-1:0]),
    .spr_bus_ack_o		(spr_bus_ack_ic_i),
    // Inputs
    .ic_enable			(spr_sr_o[`OR1K_SPR_SR_ICE]),
    .pc_addr_i			(pc_addr_o[OPTION_OPERAND_WIDTH-1:0]),
    .pc_fetch_i			(pc_fetch_o[OPTION_OPERAND_WIDTH-1:0]),
    .padv_fetch_i		(padv_fetch_o),
    .cpu_adr_i			(ic_adr_i[OPTION_OPERAND_WIDTH-1:0]),
    .spr_bus_addr_i		(spr_bus_addr_o[15:0]),
    .spr_bus_we_i		(spr_bus_we_o),
    .spr_bus_stb_i		(spr_bus_stb_o),
    .spr_bus_dat_i		(spr_bus_dat_o[OPTION_OPERAND_WIDTH-1:0]),
    );*/

   mor1kx_icache
     #(
       .FEATURE_INSTRUCTIONCACHE(FEATURE_INSTRUCTIONCACHE),
       .OPTION_ICACHE_BLOCK_WIDTH(OPTION_ICACHE_BLOCK_WIDTH),
       .OPTION_ICACHE_SET_WIDTH(OPTION_ICACHE_SET_WIDTH),
       .OPTION_ICACHE_WAYS(OPTION_ICACHE_WAYS),
       .OPTION_ICACHE_LIMIT_WIDTH(OPTION_ICACHE_LIMIT_WIDTH)
       )
   mor1kx_icache
     (/*AUTOINST*/
      // Outputs
      .cpu_err_o			(ic_err_o),		 // Templated
      .cpu_ack_o			(ic_ack_o),		 // Templated
      .cpu_dat_o			(ic_dat_o[OPTION_OPERAND_WIDTH-1:0]), // Templated
      .ibus_adr_o			(ibus_adr_o[31:0]),
      .ibus_req_o			(ibus_req_o),
      .spr_bus_dat_o			(spr_bus_dat_ic_i[OPTION_OPERAND_WIDTH-1:0]), // Templated
      .spr_bus_ack_o			(spr_bus_ack_ic_i),	 // Templated
      // Inputs
      .clk				(clk),
      .rst				(rst),
      .ic_enable			(spr_sr_o[`OR1K_SPR_SR_ICE]), // Templated
      .pc_addr_i			(pc_addr_o[OPTION_OPERAND_WIDTH-1:0]), // Templated
      .pc_fetch_i			(pc_fetch_o[OPTION_OPERAND_WIDTH-1:0]), // Templated
      .padv_fetch_i			(padv_fetch_o),		 // Templated
      .ibus_err_i			(ibus_err_i),
      .ibus_ack_i			(ibus_ack_i),
      .ibus_dat_i			(ibus_dat_i[31:0]),
      .spr_bus_addr_i			(spr_bus_addr_o[15:0]),	 // Templated
      .spr_bus_we_i			(spr_bus_we_o),		 // Templated
      .spr_bus_stb_i			(spr_bus_stb_o),	 // Templated
      .spr_bus_dat_i			(spr_bus_dat_o[OPTION_OPERAND_WIDTH-1:0])); // Templated

   /* mor1kx_decode AUTO_TEMPLATE (
    .padv_i				(padv_decode_o),
    .pc_decode_i			(pc_fetch_to_decode),
    .decode_insn_i			(insn_fetch_to_decode),
    .decode_except_ibus_err_i		(decode_except_ibus_err_o),
    .pipeline_flush_i			(pipeline_flush_o),
    .pc_execute_o                       (pc_decode_to_execute),
    ); */
   mor1kx_decode
     #(
       .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH),
       .OPTION_RESET_PC(OPTION_RESET_PC),
       .OPTION_RF_ADDR_WIDTH(OPTION_RF_ADDR_WIDTH),
       .FEATURE_SYSCALL(FEATURE_SYSCALL),
       .FEATURE_TRAP(FEATURE_TRAP),
       .FEATURE_RANGE(FEATURE_RANGE),
       .FEATURE_MAC(FEATURE_MAC),
       .FEATURE_MULTIPLIER(FEATURE_MULTIPLIER),
       .FEATURE_DIVIDER(FEATURE_DIVIDER),
       .FEATURE_ADDC(FEATURE_ADDC),
       .FEATURE_SRA(FEATURE_SRA),
       .FEATURE_ROR(FEATURE_ROR),
       .FEATURE_EXT(FEATURE_EXT),
       .FEATURE_CMOV(FEATURE_CMOV),
       .FEATURE_FFL1(FEATURE_FFL1),
       .FEATURE_CUST1(FEATURE_CUST1),
       .FEATURE_CUST2(FEATURE_CUST2),
       .FEATURE_CUST3(FEATURE_CUST3),
       .FEATURE_CUST4(FEATURE_CUST4),
       .FEATURE_CUST5(FEATURE_CUST5),
       .FEATURE_CUST6(FEATURE_CUST6),
       .FEATURE_CUST7(FEATURE_CUST7),
       .FEATURE_CUST8(FEATURE_CUST8)
       )
     mor1kx_decode 
     (/*AUTOINST*/
      // Outputs
      .opc_alu_o			(opc_alu_o[`OR1K_ALU_OPC_WIDTH-1:0]),
      .opc_alu_secondary_o		(opc_alu_secondary_o[`OR1K_ALU_OPC_WIDTH-1:0]),
      .imm16_o				(imm16_o[`OR1K_IMM_WIDTH-1:0]),
      .immjbr_upper_o			(immjbr_upper_o[9:0]),
      .rfd_adr_o			(rfd_adr_o[OPTION_RF_ADDR_WIDTH-1:0]),
      .rfa_adr_o			(rfa_adr_o[OPTION_RF_ADDR_WIDTH-1:0]),
      .rfb_adr_o			(rfb_adr_o[OPTION_RF_ADDR_WIDTH-1:0]),
      .rf_wb_o				(rf_wb_o),
      .op_jbr_o				(op_jbr_o),
      .op_jr_o				(op_jr_o),
      .op_jal_o				(op_jal_o),
      .op_alu_o				(op_alu_o),
      .op_lsu_load_o			(op_lsu_load_o),
      .op_lsu_store_o			(op_lsu_store_o),
      .op_mfspr_o			(op_mfspr_o),
      .execute_except_ibus_err_o	(execute_except_ibus_err_o),
      .execute_except_illegal_o		(execute_except_illegal_o),
      .execute_except_syscall_o		(execute_except_syscall_o),
      .execute_except_trap_o		(execute_except_trap_o),
      .pc_execute_o			(pc_decode_to_execute),	 // Templated
      .decode_valid_o			(decode_valid_o),
      .opc_insn_o			(opc_insn_o[`OR1K_OPCODE_WIDTH-1:0]),
      // Inputs
      .clk				(clk),
      .rst				(rst),
      .padv_i				(padv_decode_o),	 // Templated
      .pc_decode_i			(pc_fetch_to_decode),	 // Templated
      .decode_insn_i			(insn_fetch_to_decode),	 // Templated
      .pipeline_flush_i			(pipeline_flush_o),	 // Templated
      .decode_except_ibus_err_i		(decode_except_ibus_err_o)); // Templated
   
   /* mor1kx_execute_alu AUTO_TEMPLATE (
    .padv_i				(padv_execute_o),    
    .opc_alu_i			        (opc_alu_o),
    .opc_alu_secondary_i		(opc_alu_secondary_o),
    .imm16_i				(imm16_o),
    .opc_insn_i			        (opc_insn_o),
    .decode_valid_i			(decode_valid_o),
    .op_jbr_i				(op_jbr_o),
    .op_jr_i				(op_jr_o),
    .immjbr_upper_i			(immjbr_upper_o),
    .pc_execute_i			(pc_decode_to_execute),
    .rfa_i				(rfa_o),
    .rfb_i				(rfb_o),
    .flag_i				(ctrl_flag_o),
    ); */
   mor1kx_execute_alu
     #(
       .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH),
       .FEATURE_MULTIPLIER(FEATURE_MULTIPLIER),
       .FEATURE_DIVIDER(FEATURE_DIVIDER),
       .FEATURE_ADDC(FEATURE_ADDC),
       .FEATURE_SRA(FEATURE_SRA),
       .FEATURE_ROR(FEATURE_ROR),
       .FEATURE_EXT(FEATURE_EXT),
       .FEATURE_CMOV(FEATURE_CMOV),
       .FEATURE_FFL1(FEATURE_FFL1),
       .FEATURE_CUST1(FEATURE_CUST1),
       .FEATURE_CUST2(FEATURE_CUST2),
       .FEATURE_CUST3(FEATURE_CUST3),
       .FEATURE_CUST4(FEATURE_CUST4),
       .FEATURE_CUST5(FEATURE_CUST5),
       .FEATURE_CUST6(FEATURE_CUST6),
       .FEATURE_CUST7(FEATURE_CUST7),
       .FEATURE_CUST8(FEATURE_CUST8),
       .OPTION_SHIFTER(OPTION_SHIFTER)
       )
     mor1kx_execute_alu 
     (/*AUTOINST*/
      // Outputs
      .flag_set_o			(flag_set_o),
      .flag_clear_o			(flag_clear_o),
      .alu_result_o			(alu_result_o[OPTION_OPERAND_WIDTH-1:0]),
      .alu_valid_o			(alu_valid_o),
      // Inputs
      .clk				(clk),
      .rst				(rst),
      .padv_i				(padv_execute_o),	 // Templated
      .opc_alu_i			(opc_alu_o),		 // Templated
      .opc_alu_secondary_i		(opc_alu_secondary_o),	 // Templated
      .imm16_i				(imm16_o),		 // Templated
      .opc_insn_i			(opc_insn_o),		 // Templated
      .decode_valid_i			(decode_valid_o),	 // Templated
      .op_jbr_i				(op_jbr_o),		 // Templated
      .op_jr_i				(op_jr_o),		 // Templated
      .immjbr_upper_i			(immjbr_upper_o),	 // Templated
      .pc_execute_i			(pc_decode_to_execute),	 // Templated
      .rfa_i				(rfa_o),		 // Templated
      .rfb_i				(rfb_o),		 // Templated
      .flag_i				(ctrl_flag_o));		 // Templated

   
   /* mor1kx_lsu_cappuccino AUTO_TEMPLATE (
    .padv_execute_i			(padv_execute_o),
    .decode_valid_i			(decode_valid_o),
    .alu_result_i			(alu_result_o),
    .rfb_i				(rfb_o),
    .opc_insn_i			        (opc_insn_o),
    .op_lsu_load_i			(op_lsu_load_o),
    .op_lsu_store_i			(op_lsu_store_o),
    .pipeline_flush_i			(pipeline_flush_o),
    ); */
   mor1kx_lsu_cappuccino
     #(
       .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH)
       )
     mor1kx_lsu_cappuccino 
     (/*AUTOINST*/
      // Outputs
      .lsu_result_o			(lsu_result_o[OPTION_OPERAND_WIDTH-1:0]),
      .lsu_valid_o			(lsu_valid_o),
      .lsu_except_dbus_o		(lsu_except_dbus_o),
      .lsu_except_align_o		(lsu_except_align_o),
      .dbus_adr_o			(dbus_adr_o[OPTION_OPERAND_WIDTH-1:0]),
      .dbus_req_o			(dbus_req_o),
      .dbus_dat_o			(dbus_dat_o[OPTION_OPERAND_WIDTH-1:0]),
      .dbus_bsel_o			(dbus_bsel_o[3:0]),
      .dbus_we_o			(dbus_we_o),
      // Inputs
      .clk				(clk),
      .rst				(rst),
      .padv_execute_i			(padv_execute_o),	 // Templated
      .decode_valid_i			(decode_valid_o),	 // Templated
      .alu_result_i			(alu_result_o),		 // Templated
      .rfb_i				(rfb_o),		 // Templated
      .opc_insn_i			(opc_insn_o),		 // Templated
      .op_lsu_load_i			(op_lsu_load_o),	 // Templated
      .op_lsu_store_i			(op_lsu_store_o),	 // Templated
      .dbus_err_i			(dbus_err_i),
      .dbus_ack_i			(dbus_ack_i),
      .dbus_dat_i			(dbus_dat_i[OPTION_OPERAND_WIDTH-1:0]),
      .pipeline_flush_i			(pipeline_flush_o));	 // Templated

   
   /* mor1kx_wb_mux_cappuccino AUTO_TEMPLATE (
    .alu_result_i			(alu_result_o),
    .lsu_result_i			(lsu_result_o),
    .spr_i				(mfspr_dat_o),
    .op_jal_i				(op_jal_o),    
    .op_lsu_load_i			(op_lsu_load_o),
    .pc_execute_i			(pc_decode_to_execute),
    .op_mfspr_i			        (op_mfspr_o),
    ); */
   mor1kx_wb_mux_cappuccino
     #(
       .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH)
       )
     mor1kx_wb_mux_cappuccino 
     (/*AUTOINST*/
      // Outputs
      .rf_result_o			(rf_result_o[OPTION_OPERAND_WIDTH-1:0]),
      // Inputs
      .clk				(clk),
      .rst				(rst),
      .alu_result_i			(alu_result_o),		 // Templated
      .lsu_result_i			(lsu_result_o),		 // Templated
      .pc_execute_i			(pc_decode_to_execute),	 // Templated
      .spr_i				(mfspr_dat_o),		 // Templated
      .op_jal_i				(op_jal_o),		 // Templated
      .op_lsu_load_i			(op_lsu_load_o),	 // Templated
      .op_mfspr_i			(op_mfspr_o));		 // Templated
   
   
   /* mor1kx_rf_cappuccino AUTO_TEMPLATE (
    .padv_execute_i			(padv_execute_o),
    .padv_decode_i			(padv_decode_o),
    .rfd_adr_i  			(rfd_adr_o),
    .rfa_adr_i  			(rfa_adr_o),
    .rfb_adr_i  			(rfb_adr_o),
    .execute_rf_we_i			(execute_rf_we_o),
    .result_i				(rf_result_o),
    .write_mask_i			(1'b0),
    .rf_wb_i				(rf_wb_o),
    ); */
   mor1kx_rf_cappuccino
     #(
       .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH),
       .OPTION_RF_ADDR_WIDTH(OPTION_RF_ADDR_WIDTH),
       .OPTION_RF_WORDS(OPTION_RF_WORDS)
       )
     mor1kx_rf_cappuccino 
     (/*AUTOINST*/
      // Outputs
      .rfa_o				(rfa_o[OPTION_OPERAND_WIDTH-1:0]),
      .rfb_o				(rfb_o[OPTION_OPERAND_WIDTH-1:0]),
      // Inputs
      .clk				(clk),
      .rst				(rst),
      .padv_execute_i			(padv_execute_o),	 // Templated
      .padv_decode_i			(padv_decode_o),	 // Templated
      .rfd_adr_i			(rfd_adr_o),		 // Templated
      .rfa_adr_i			(rfa_adr_o),		 // Templated
      .rfb_adr_i			(rfb_adr_o),		 // Templated
      .rf_wb_i				(rf_wb_o),		 // Templated
      .execute_rf_we_i			(execute_rf_we_o),	 // Templated
      .result_i				(rf_result_o),		 // Templated
      .write_mask_i			(1'b0));			 // Templated

   	 
   /* Debug signals required for the debug monitor */
   function [OPTION_OPERAND_WIDTH-1:0] get_gpr;
      // verilator public
      input [4:0] 		   gpr_num;
      begin
	 get_gpr = mor1kx_rf_cappuccino.rfa.ram[gpr_num];
      end
   endfunction //
   
   
   function set_gpr;
      // verilator public
      input [4:0] gpr_num;
      input [OPTION_OPERAND_WIDTH-1:0] gpr_value;
      begin
	 mor1kx_rf_cappuccino.rfa.ram[gpr_num] = gpr_value;
	 set_gpr = 1;
      end
   endfunction

   
   /* mor1kx_execute_ctrl_cappuccino AUTO_TEMPLATE (
    .padv_i				(padv_execute_o),    
    .opc_insn_i 			(opc_insn_o),
    .execute_except_ibus_err_i		(execute_except_ibus_err_o),
    .execute_except_illegal_i		(execute_except_illegal_o),
    .execute_except_syscall_i		(execute_except_syscall_o),
    .execute_except_trap_i		(execute_except_trap_o),
    .lsu_except_dbus_i  		(lsu_except_dbus_o),
    .lsu_except_align_i			(lsu_except_align_o),
    .op_alu_i				(op_alu_o),
    .op_lsu_load_i			(op_lsu_load_o),
    .op_lsu_store_i			(op_lsu_store_o),
    .alu_valid_i			(alu_valid_o),
    .lsu_valid_i			(lsu_valid_o),
    .alu_result_i			(alu_result_o),
    .op_jr_i				(op_jr_o),
    .rfb_i				(rfb_o),
    .flag_set_i 			(flag_set_o),
    .flag_clear_i			(flag_clear_o),
    .pc_execute_i			(pc_decode_to_execute),
    .rf_wb_i				(rf_wb_o),
    .ctrl_mfspr_we_i			(ctrl_mfspr_we_o),
    .pipeline_flush_i			(pipeline_flush_o),
    .pc_ctrl_o                          (pc_execute_to_ctrl),
    ); */
   mor1kx_execute_ctrl_cappuccino
     #(
       .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH),
       .OPTION_RESET_PC(OPTION_RESET_PC)
       )
     mor1kx_execute_ctrl_cappuccino 
     (/*AUTOINST*/
      // Outputs
      .execute_rf_we_o			(execute_rf_we_o),
      .execute_except_ibus_align_o	(execute_except_ibus_align_o),
      .ctrl_alu_result_o		(ctrl_alu_result_o[OPTION_OPERAND_WIDTH-1:0]),
      .ctrl_rfb_o			(ctrl_rfb_o[OPTION_OPERAND_WIDTH-1:0]),
      .ctrl_flag_set_o			(ctrl_flag_set_o),
      .ctrl_flag_clear_o		(ctrl_flag_clear_o),
      .pc_ctrl_o			(pc_execute_to_ctrl),	 // Templated
      .ctrl_opc_insn_o			(ctrl_opc_insn_o[`OR1K_OPCODE_WIDTH-1:0]),
      .ctrl_except_ibus_err_o		(ctrl_except_ibus_err_o),
      .ctrl_except_ibus_align_o		(ctrl_except_ibus_align_o),
      .ctrl_except_illegal_o		(ctrl_except_illegal_o),
      .ctrl_except_syscall_o		(ctrl_except_syscall_o),
      .ctrl_except_dbus_o		(ctrl_except_dbus_o),
      .ctrl_except_align_o		(ctrl_except_align_o),
      .ctrl_except_trap_o		(ctrl_except_trap_o),
      .execute_waiting_o		(execute_waiting_o),
      .execute_valid_o			(execute_valid_o),
      // Inputs
      .clk				(clk),
      .rst				(rst),
      .padv_i				(padv_execute_o),	 // Templated
      .opc_insn_i			(opc_insn_o),		 // Templated
      .execute_except_ibus_err_i	(execute_except_ibus_err_o), // Templated
      .execute_except_illegal_i		(execute_except_illegal_o), // Templated
      .execute_except_syscall_i		(execute_except_syscall_o), // Templated
      .lsu_except_dbus_i		(lsu_except_dbus_o),	 // Templated
      .lsu_except_align_i		(lsu_except_align_o),	 // Templated
      .execute_except_trap_i		(execute_except_trap_o), // Templated
      .pipeline_flush_i			(pipeline_flush_o),	 // Templated
      .op_alu_i				(op_alu_o),		 // Templated
      .op_lsu_load_i			(op_lsu_load_o),	 // Templated
      .op_lsu_store_i			(op_lsu_store_o),	 // Templated
      .alu_valid_i			(alu_valid_o),		 // Templated
      .lsu_valid_i			(lsu_valid_o),		 // Templated
      .op_jr_i				(op_jr_o),		 // Templated
      .alu_result_i			(alu_result_o),		 // Templated
      .rfb_i				(rfb_o),		 // Templated
      .flag_set_i			(flag_set_o),		 // Templated
      .flag_clear_i			(flag_clear_o),		 // Templated
      .pc_execute_i			(pc_decode_to_execute),	 // Templated
      .rf_wb_i				(rf_wb_o),		 // Templated
      .ctrl_mfspr_we_i			(ctrl_mfspr_we_o));	 // Templated

   /* mor1kx_ctrl_branch_cappuccino AUTO_TEMPLATE (
    .ex_alu_result_i			(alu_result_o),
    .ex_rfb_i				(rfb_o),
    .op_jbr_i				(op_jbr_o),
    .op_jr_i				(op_jr_o),
    .execute_opc_insn_i			(opc_insn_o),
    .ctrl_flag_i			(ctrl_flag_o),
    .ctrl_branch_exception_i		(ctrl_branch_exception_o),
    .ctrl_branch_except_pc_i		(ctrl_branch_except_pc_o),
    .ctrl_except_ibus_align_i		(ctrl_except_ibus_align_o),
    .execute_except_ibus_align_i	(execute_except_ibus_align_o),
    ); */
   mor1kx_ctrl_branch_cappuccino
     #(
       .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH)
       )
     mor1kx_ctrl_branch_cappuccino
     (/*AUTOINST*/
      // Outputs
      .ctrl_branch_occur_o		(ctrl_branch_occur_o),
      .ctrl_branch_target_o		(ctrl_branch_target_o[OPTION_OPERAND_WIDTH-1:0]),
      // Inputs
      .clk				(clk),
      .rst				(rst),
      .ex_alu_result_i			(alu_result_o),		 // Templated
      .ex_rfb_i				(rfb_o),		 // Templated
      .op_jbr_i				(op_jbr_o),		 // Templated
      .op_jr_i				(op_jr_o),		 // Templated
      .execute_opc_insn_i		(opc_insn_o),		 // Templated
      .ctrl_flag_i			(ctrl_flag_o),		 // Templated
      .ctrl_branch_exception_i		(ctrl_branch_exception_o), // Templated
      .ctrl_branch_except_pc_i		(ctrl_branch_except_pc_o), // Templated
      .execute_except_ibus_align_i	(execute_except_ibus_align_o), // Templated
      .ctrl_except_ibus_align_i		(ctrl_except_ibus_align_o)); // Templated
   

   /* mor1kx_ctrl_cappuccino AUTO_TEMPLATE (   
    .ctrl_alu_result_i		(ctrl_alu_result_o),
    .ctrl_rfb_i			(ctrl_rfb_o),
    .ctrl_flag_set_i		(ctrl_flag_set_o),
    .ctrl_flag_clear_i		(ctrl_flag_clear_o),
    .pc_ctrl_i			(pc_execute_to_ctrl),
    .pc_execute_i		(pc_decode_to_execute),    
    .ctrl_opc_insn_i		(ctrl_opc_insn_o),
    .ctrl_branch_occur_i	(ctrl_branch_occur_o),
    .ctrl_branch_target_i	(ctrl_branch_target_o),
    .except_ibus_err_i		(ctrl_except_ibus_err_o),
    .except_ibus_align_i	(ctrl_except_ibus_align_o),
    .except_illegal_i		(ctrl_except_illegal_o),
    .except_syscall_i		(ctrl_except_syscall_o),
    .except_dbus_i		(ctrl_except_dbus_o),
    .except_trap_i		(ctrl_except_trap_o),
    .except_align_i		(ctrl_except_align_o),
    .fetch_valid_i		(fetch_valid_o),
    .decode_valid_i		(decode_valid_o),
    .execute_valid_i		(execute_valid_o),
    .execute_waiting_i		(execute_waiting_o),
    .execute_opc_insn_i		(opc_insn_o),    
    .fetch_branch_taken_i	(fetch_branch_taken_o),
    ) */
   mor1kx_ctrl_cappuccino
     #(
       .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH),
       .OPTION_RESET_PC(OPTION_RESET_PC),
       .FEATURE_PIC(FEATURE_PIC),
       .FEATURE_TIMER(FEATURE_TIMER),
       .OPTION_PIC_TRIGGER(OPTION_PIC_TRIGGER),
       .FEATURE_DATACACHE(FEATURE_DATACACHE),
       .OPTION_DCACHE_BLOCK_WIDTH(OPTION_DCACHE_BLOCK_WIDTH),
       .OPTION_DCACHE_SET_WIDTH(OPTION_DCACHE_SET_WIDTH),
       .OPTION_DCACHE_WAYS(OPTION_DCACHE_WAYS),
       .FEATURE_DMMU(FEATURE_DMMU),
       .FEATURE_INSTRUCTIONCACHE(FEATURE_INSTRUCTIONCACHE),
       .OPTION_ICACHE_BLOCK_WIDTH(OPTION_ICACHE_BLOCK_WIDTH),
       .OPTION_ICACHE_SET_WIDTH(OPTION_ICACHE_SET_WIDTH),
       .OPTION_ICACHE_WAYS(OPTION_ICACHE_WAYS),
       .FEATURE_IMMU(FEATURE_IMMU),
       .FEATURE_DEBUGUNIT(FEATURE_DEBUGUNIT),
       .FEATURE_PERFCOUNTERS(FEATURE_PERFCOUNTERS),
       .FEATURE_MAC(FEATURE_MAC),
       .FEATURE_SYSCALL(FEATURE_SYSCALL),
       .FEATURE_TRAP(FEATURE_TRAP),
       .FEATURE_RANGE(FEATURE_RANGE),
       .FEATURE_DSX(FEATURE_DSX)
       )
     mor1kx_ctrl_cappuccino 
     (/*AUTOINST*/
      // Outputs
      .mfspr_dat_o			(mfspr_dat_o[OPTION_OPERAND_WIDTH-1:0]),
      .ctrl_mfspr_we_o			(ctrl_mfspr_we_o),
      .ctrl_flag_o			(ctrl_flag_o),
      .ctrl_branch_exception_o		(ctrl_branch_exception_o),
      .ctrl_branch_except_pc_o		(ctrl_branch_except_pc_o[OPTION_OPERAND_WIDTH-1:0]),
      .pipeline_flush_o			(pipeline_flush_o),
      .padv_fetch_o			(padv_fetch_o),
      .padv_decode_o			(padv_decode_o),
      .padv_execute_o			(padv_execute_o),
      .du_dat_o				(du_dat_o[OPTION_OPERAND_WIDTH-1:0]),
      .du_ack_o				(du_ack_o),
      .du_stall_o			(du_stall_o),
      .du_restart_pc_o			(du_restart_pc_o[OPTION_OPERAND_WIDTH-1:0]),
      .du_restart_o			(du_restart_o),
      .spr_bus_addr_o			(spr_bus_addr_o[15:0]),
      .spr_bus_we_o			(spr_bus_we_o),
      .spr_bus_stb_o			(spr_bus_stb_o),
      .spr_bus_dat_o			(spr_bus_dat_o[OPTION_OPERAND_WIDTH-1:0]),
      .spr_sr_o				(spr_sr_o[15:0]),
      // Inputs
      .clk				(clk),
      .rst				(rst),
      .ctrl_alu_result_i		(ctrl_alu_result_o),	 // Templated
      .ctrl_rfb_i			(ctrl_rfb_o),		 // Templated
      .ctrl_flag_set_i			(ctrl_flag_set_o),	 // Templated
      .ctrl_flag_clear_i		(ctrl_flag_clear_o),	 // Templated
      .pc_ctrl_i			(pc_execute_to_ctrl),	 // Templated
      .ctrl_opc_insn_i			(ctrl_opc_insn_o),	 // Templated
      .ctrl_branch_occur_i		(ctrl_branch_occur_o),	 // Templated
      .ctrl_branch_target_i		(ctrl_branch_target_o),	 // Templated
      .pc_execute_i			(pc_decode_to_execute),	 // Templated
      .execute_opc_insn_i		(opc_insn_o),		 // Templated
      .except_ibus_err_i		(ctrl_except_ibus_err_o), // Templated
      .except_ibus_align_i		(ctrl_except_ibus_align_o), // Templated
      .except_illegal_i			(ctrl_except_illegal_o), // Templated
      .except_syscall_i			(ctrl_except_syscall_o), // Templated
      .except_dbus_i			(ctrl_except_dbus_o),	 // Templated
      .except_trap_i			(ctrl_except_trap_o),	 // Templated
      .except_align_i			(ctrl_except_align_o),	 // Templated
      .fetch_valid_i			(fetch_valid_o),	 // Templated
      .decode_valid_i			(decode_valid_o),	 // Templated
      .execute_valid_i			(execute_valid_o),	 // Templated
      .execute_waiting_i		(execute_waiting_o),	 // Templated
      .fetch_branch_taken_i		(fetch_branch_taken_o),	 // Templated
      .irq_i				(irq_i[31:0]),
      .du_addr_i			(du_addr_i[15:0]),
      .du_stb_i				(du_stb_i),
      .du_dat_i				(du_dat_i[OPTION_OPERAND_WIDTH-1:0]),
      .du_we_i				(du_we_i),
      .du_stall_i			(du_stall_i),
      .spr_bus_dat_dc_i			(spr_bus_dat_dc_i[OPTION_OPERAND_WIDTH-1:0]),
      .spr_bus_ack_dc_i			(spr_bus_ack_dc_i),
      .spr_bus_dat_ic_i			(spr_bus_dat_ic_i[OPTION_OPERAND_WIDTH-1:0]),
      .spr_bus_ack_ic_i			(spr_bus_ack_ic_i),
      .spr_bus_dat_dmmu_i		(spr_bus_dat_dmmu_i[OPTION_OPERAND_WIDTH-1:0]),
      .spr_bus_ack_dmmu_i		(spr_bus_ack_dmmu_i),
      .spr_bus_dat_immu_i		(spr_bus_dat_immu_i[OPTION_OPERAND_WIDTH-1:0]),
      .spr_bus_ack_immu_i		(spr_bus_ack_immu_i),
      .spr_bus_dat_mac_i		(spr_bus_dat_mac_i[OPTION_OPERAND_WIDTH-1:0]),
      .spr_bus_ack_mac_i		(spr_bus_ack_mac_i),
      .spr_bus_dat_pmu_i		(spr_bus_dat_pmu_i[OPTION_OPERAND_WIDTH-1:0]),
      .spr_bus_ack_pmu_i		(spr_bus_ack_pmu_i),
      .spr_bus_dat_pcu_i		(spr_bus_dat_pcu_i[OPTION_OPERAND_WIDTH-1:0]),
      .spr_bus_ack_pcu_i		(spr_bus_ack_pcu_i),
      .spr_bus_dat_fpu_i		(spr_bus_dat_fpu_i[OPTION_OPERAND_WIDTH-1:0]),
      .spr_bus_ack_fpu_i		(spr_bus_ack_fpu_i));

endmodule // mor1kx_cpu_cappuccino
