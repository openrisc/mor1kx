/* ****************************************************************************
  This Source Code Form is subject to the terms of the
  Open Hardware Description License, v. 1.0. If a copy
  of the OHDL was not distributed with this file, You
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: mor1kx control unit

  inputs from execute stage

  generate pipeline controls

  manage SPRs

  issue addresses for exceptions to fetch stage
  control branches going to fetch stage

  contains tick timer

  contains PIC logic

  Copyright (C) 2012 Authors

  Author(s): Julius Baxter <juliusbaxter@gmail.com>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_ctrl_cappuccino
  #(
    parameter OPTION_OPERAND_WIDTH = 32,
    parameter OPTION_RESET_PC = {{(OPTION_OPERAND_WIDTH-13){1'b0}},
				 `OR1K_RESET_VECTOR,8'd0},

    parameter FEATURE_SYSCALL = "ENABLED",
    parameter FEATURE_TRAP = "ENABLED",
    parameter FEATURE_RANGE = "ENABLED",

    parameter FEATURE_DATACACHE = "NONE",
    parameter OPTION_DCACHE_BLOCK_WIDTH = 5,
    parameter OPTION_DCACHE_SET_WIDTH = 9,
    parameter OPTION_DCACHE_WAYS = 2,
    parameter FEATURE_DMMU = "NONE",
    parameter OPTION_DMMU_SET_WIDTH = 6,
    parameter OPTION_DMMU_WAYS = 1,
    parameter FEATURE_INSTRUCTIONCACHE = "NONE",
    parameter OPTION_ICACHE_BLOCK_WIDTH = 5,
    parameter OPTION_ICACHE_SET_WIDTH = 9,
    parameter OPTION_ICACHE_WAYS = 2,
    parameter FEATURE_IMMU = "NONE",
    parameter OPTION_IMMU_SET_WIDTH = 6,
    parameter OPTION_IMMU_WAYS = 1,
    parameter FEATURE_PIC = "ENABLED",
    parameter FEATURE_TIMER = "ENABLED",
    parameter FEATURE_DEBUGUNIT = "NONE",
    parameter FEATURE_PERFCOUNTERS = "NONE",
    parameter FEATURE_PMU = "NONE",
    parameter FEATURE_MAC = "NONE",
    parameter FEATURE_FPU = "NONE",

    parameter OPTION_PIC_TRIGGER = "EDGE",

    parameter FEATURE_DSX ="NONE",
    parameter FEATURE_FASTCONTEXTS = "NONE",
    parameter FEATURE_OVERFLOW = "NONE",

    parameter SPR_SR_WIDTH = 16,
    parameter SPR_SR_RESET_VALUE = 16'h8001
    )
   (
    input 			      clk,
    input 			      rst,

    // ALU result - either jump target, SPR address
    input [OPTION_OPERAND_WIDTH-1:0]  ctrl_alu_result_i,

    // LSU address, needed for effective address
    input [OPTION_OPERAND_WIDTH-1:0]  ctrl_lsu_adr_i,

    // Operand B from RF might be jump address, might be value for SPR
    input [OPTION_OPERAND_WIDTH-1:0]  ctrl_rfb_i,

    input 			      ctrl_flag_set_i,
    input 			      ctrl_flag_clear_i,

    input [OPTION_OPERAND_WIDTH-1:0]  pc_ctrl_i,

    input 			      ctrl_op_mfspr_i,
    input 			      ctrl_op_mtspr_i,
    input 			      ctrl_op_rfe_i,

    // Indicate if branch will be taken based on instruction currently in
    // decode stage.
    input 			      decode_branch_i,
    input [OPTION_OPERAND_WIDTH-1:0]  decode_branch_target_i,

    input 			      branch_mispredict_i,
    input [OPTION_OPERAND_WIDTH-1:0]  execute_mispredict_target_i,

    // PC of execute stage (NPC)
    input [OPTION_OPERAND_WIDTH-1:0]  pc_execute_i,

    input 			      execute_op_branch_i,

    // Exception inputs, registered on output of execute stage
    input 			      except_ibus_err_i,
    input 			      except_itlb_miss_i,
    input 			      except_ipagefault_i,
    input 			      except_ibus_align_i,
    input 			      except_illegal_i,
    input 			      except_syscall_i,
    input 			      except_dbus_i,
    input 			      except_dtlb_miss_i,
    input 			      except_dpagefault_i,
    input 			      except_trap_i,
    input 			      except_align_i,

    // Inputs from two units that can stall proceedings
    input 			      fetch_valid_i,
    input 			      decode_valid_i,
    input 			      execute_valid_i,
    input 			      execute_waiting_i,

    input 			      fetch_exception_taken_i,

    input 			      decode_bubble_i,
    input 			      execute_bubble_i,

    // External IRQ lines in
    input [31:0] 		      irq_i,

    // Exception PC output, used in the lsu to properly signal dbus errors that
    // has went through the store buffer
    output [OPTION_OPERAND_WIDTH-1:0] ctrl_epcr_o,
    // Exception PC input coming from the store buffer
    input [OPTION_OPERAND_WIDTH-1:0]  store_buffer_epcr_i,

    input 			      store_buffer_err_i,

    // SPR data out
    output [OPTION_OPERAND_WIDTH-1:0] mfspr_dat_o,

    // WE to RF for l.mfspr
    output 			      ctrl_mfspr_ack_o,
    output 			      ctrl_mtspr_ack_o,

    // Flag out to branch control, combinatorial
    output 			      ctrl_flag_o,

    // Arithmetic flags to and from ALU
    output 			      ctrl_carry_o,
    input 			      ctrl_carry_set_i,
    input 			      ctrl_carry_clear_i,
    input 			      ctrl_overflow_set_i,
    input 			      ctrl_overflow_clear_i,

    // Branch indicator from control unit (l.rfe/exception)
    output 			      ctrl_branch_exception_o,
    // PC out to fetch stage for l.rfe, exceptions
    output [OPTION_OPERAND_WIDTH-1:0] ctrl_branch_except_pc_o,

    // Clear instructions from decode and fetch stage
    output 			      pipeline_flush_o,

    // Indicate that a rfe is going on
    output 			      doing_rfe_o,

    output 			      padv_fetch_o,
    output 			      padv_decode_o,
    output 			      padv_execute_o,
    output 			      padv_ctrl_o,

    // Debug bus
    input [15:0] 		      du_addr_i,
    input 			      du_stb_i,
    input [OPTION_OPERAND_WIDTH-1:0]  du_dat_i,
    input 			      du_we_i,
    output [OPTION_OPERAND_WIDTH-1:0] du_dat_o,
    output 			      du_ack_o,
    // Stall control from debug interface
    input 			      du_stall_i,
    output 			      du_stall_o,
    output [OPTION_OPERAND_WIDTH-1:0] du_restart_pc_o,
    output 			      du_restart_o,

    // SPR accesses to external units (cache, mmu, etc.)
    output [15:0] 		      spr_bus_addr_o,
    output 			      spr_bus_we_o,
    output 			      spr_bus_stb_o,
    output [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o,
    input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_dc_i,
    input 			      spr_bus_ack_dc_i,
    input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_ic_i,
    input 			      spr_bus_ack_ic_i,
    input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_dmmu_i,
    input 			      spr_bus_ack_dmmu_i,
    input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_immu_i,
    input 			      spr_bus_ack_immu_i,
    input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_mac_i,
    input 			      spr_bus_ack_mac_i,
    input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_pmu_i,
    input 			      spr_bus_ack_pmu_i,
    input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_pcu_i,
    input 			      spr_bus_ack_pcu_i,
    input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_fpu_i,
    input 			      spr_bus_ack_fpu_i,
    output [15:0] 		      spr_sr_o
    );

   // Internal signals
   reg [SPR_SR_WIDTH-1:0] 	     spr_sr;
   reg [SPR_SR_WIDTH-1:0] 	     spr_esr;
   reg [OPTION_OPERAND_WIDTH-1:0]    spr_epcr;
   reg [OPTION_OPERAND_WIDTH-1:0]    spr_eear;
   reg [OPTION_OPERAND_WIDTH-1:0]    spr_evbar;

   // Programmable Interrupt Control SPRs
   wire [31:0] 			     spr_picmr;
   wire [31:0] 			     spr_picsr;

   // Tick Timer SPRs
   wire [31:0] 			     spr_ttmr;
   wire [31:0] 			     spr_ttcr;

   reg [OPTION_OPERAND_WIDTH-1:0]    spr_ppc;
   reg [OPTION_OPERAND_WIDTH-1:0]    spr_npc;
   reg 				     execute_delay_slot;
   reg 				     ctrl_delay_slot;

   reg 				     execute_waiting_r;

   reg 				     decode_execute_halt;

   reg 				     exception_taken;

   reg [OPTION_OPERAND_WIDTH-1:0]    last_branch_insn_pc;
   reg [OPTION_OPERAND_WIDTH-1:0]    last_branch_target_pc;
   reg 				     padv_ctrl;

   reg 				     exception_r;

   reg [OPTION_OPERAND_WIDTH-1:0]    exception_pc_addr;

   reg 				     waiting_for_fetch;

   reg 				     doing_rfe_r;
   wire 			     doing_rfe;
   wire 			     deassert_doing_rfe;

   wire 			     exception, exception_pending;

   reg 				     ctrl_stage_exceptions;

   wire 			     exception_re;

   wire 			     except_ticktimer;
   wire 			     except_pic;

   wire 			     except_range;

   reg 				     ctrl_bubble;

   wire [15:0] 			     spr_addr;

   wire [OPTION_OPERAND_WIDTH-1:0]   b;

   wire 			     deassert_decode_execute_halt;

   /* Debug SPRs */
   reg [31:0] 			     spr_dmr1;
   reg [31:0] 			     spr_dmr2;
   reg [31:0] 			     spr_dsr;
   reg [31:0] 			     spr_drr;

   /* DU internal control signals */
   wire 			     du_access;
   wire 			     cpu_stall;
   wire 			     du_restart_from_stall;
   wire [5:0] 			     pstep;
   wire 			     stepping;
   wire 			     stepped_into_delay_slot;
   reg 				     stepped_into_exception;
   reg 				     stepped_into_rfe;
   wire 			     du_npc_write;
   reg 				     du_npc_written;

   /* Wires for SPR management */
   wire 			     spr_group_present;
   wire [3:0] 			     spr_group;
   wire 			     spr_we;
      wire 			     spr_read;
   wire [OPTION_OPERAND_WIDTH-1:0]   spr_write_dat;
   wire [12:0] 			     spr_access_ack;
   wire [31:0] 			     spr_internal_read_dat [0:12];
   wire 			     spr_read_access;
   wire 			     spr_write_access;
   wire 			     spr_bus_access;
   reg [OPTION_OPERAND_WIDTH-1:0]    spr_sys_group_read;

   /* Wires from mor1kx_cfgrs module */
   wire [31:0] 			     spr_vr;
   wire [31:0] 			     spr_vr2;
   wire [31:0] 			     spr_avr;
   wire [31:0] 			     spr_upr;
   wire [31:0] 			     spr_cpucfgr;
   wire [31:0] 			     spr_dmmucfgr;
   wire [31:0] 			     spr_immucfgr;
   wire [31:0] 			     spr_dccfgr;
   wire [31:0] 			     spr_iccfgr;
   wire [31:0] 			     spr_dcfgr;
   wire [31:0] 			     spr_pccfgr;
   wire [31:0] 			     spr_fpcsr;
   wire [31:0] 			     spr_isr [0:7];

   assign  b = ctrl_rfb_i;

   assign ctrl_branch_exception_o = (exception_r | ctrl_op_rfe_i | doing_rfe) &
				    !exception_taken;
   assign exception_pending = (except_ibus_err_i | except_ibus_align_i |
			       except_illegal_i | except_syscall_i |
			       except_dbus_i | except_align_i |
			       except_ticktimer | except_range |
			       except_pic | except_trap_i |
			       except_itlb_miss_i | except_ipagefault_i |
			       except_dtlb_miss_i | except_dpagefault_i);

   assign exception = exception_pending &
		      (padv_ctrl & !ctrl_bubble | ctrl_stage_exceptions);

   assign exception_re = exception & !exception_r & !exception_taken;

   assign except_range = (FEATURE_RANGE!="NONE") ? spr_sr[`OR1K_SPR_SR_OVE] &&
			 (spr_sr[`OR1K_SPR_SR_OV] | ctrl_overflow_set_i) &
			 !doing_rfe : 0;

   assign deassert_decode_execute_halt = fetch_exception_taken_i &
					 decode_execute_halt;

   assign ctrl_branch_except_pc_o = (ctrl_op_rfe_i | doing_rfe) ? spr_epcr :
				    exception_pc_addr;

   assign ctrl_epcr_o = ctrl_delay_slot ? pc_ctrl_i - 4 : pc_ctrl_i;

   always @(posedge clk)
     ctrl_stage_exceptions <= except_align_i | except_dbus_i | except_range |
			      except_dtlb_miss_i | except_dpagefault_i;

   always @(posedge clk)
     if (exception & !exception_r)
       casez(
	     {
	      except_itlb_miss_i,
	      except_ipagefault_i,
	      except_ibus_err_i,
	      except_illegal_i,
	      except_align_i,
	      except_ibus_align_i,
	      except_syscall_i,
	      except_dtlb_miss_i,
	      except_dpagefault_i,
	      except_trap_i,
	      except_dbus_i,
	      except_range,
	      except_pic,
	      except_ticktimer
	      }
	     )
	 14'b1?????????????:
	   exception_pc_addr <= spr_evbar |
				{19'd0,`OR1K_ITLB_VECTOR,8'd0};
	 14'b01????????????:
	   exception_pc_addr <= spr_evbar |
				{19'd0,`OR1K_IPF_VECTOR,8'd0};
	 14'b001???????????:
	   exception_pc_addr <= spr_evbar |
				{19'd0,`OR1K_BERR_VECTOR,8'd0};
	 14'b0001??????????:
	   exception_pc_addr <= spr_evbar |
				{19'd0,`OR1K_ILLEGAL_VECTOR,8'd0};
	 14'b00001?????????,
	   14'b000001????????:
	     exception_pc_addr <= spr_evbar |
				  {19'd0,`OR1K_ALIGN_VECTOR,8'd0};
	 14'b0000001???????:
	   exception_pc_addr <= spr_evbar |
				{19'd0,`OR1K_SYSCALL_VECTOR,8'd0};
	 14'b00000001??????:
	   exception_pc_addr <= spr_evbar |
				{19'd0,`OR1K_DTLB_VECTOR,8'd0};
	 14'b000000001?????:
	   exception_pc_addr <= spr_evbar |
				{19'd0,`OR1K_DPF_VECTOR,8'd0};
	 14'b0000000001????:
	   exception_pc_addr <= spr_evbar |
				{19'd0,`OR1K_TRAP_VECTOR,8'd0};
	 14'b00000000001???:
	   exception_pc_addr <= spr_evbar |
				{19'd0,`OR1K_BERR_VECTOR,8'd0};
	 14'b000000000001??:
	   exception_pc_addr <= spr_evbar |
				{19'd0,`OR1K_RANGE_VECTOR,8'd0};
	 14'b0000000000001?:
	   exception_pc_addr <= spr_evbar |
				{19'd0,`OR1K_INT_VECTOR,8'd0};
	 //14'b00000000000001:
	 default:
	   exception_pc_addr <= spr_evbar |
				{19'd0,`OR1K_TT_VECTOR,8'd0};
       endcase // casex (...

   assign padv_fetch_o = !execute_waiting_i & !cpu_stall & !decode_bubble_i
			 & (!stepping | (stepping & pstep[0] & !fetch_valid_i));

   assign padv_decode_o = fetch_valid_i & !execute_waiting_i &
			  !decode_execute_halt & !cpu_stall
			  & (!stepping | (stepping & pstep[1]));

   assign padv_execute_o = ((decode_valid_i & !execute_waiting_i &
			     /* Stop fetch before exception branch continuing */
			     !(exception_r & fetch_exception_taken_i)) |
			    (!execute_waiting_i & execute_waiting_r &
			     fetch_valid_i) |
			    // Case where execute became ready before fetch
			    // after delay in execute stage
			    (waiting_for_fetch & fetch_valid_i)) &
			   // Not exceptions occurring
			   !decode_execute_halt & !exception_re & !ctrl_op_rfe_i
			   & !cpu_stall & (!stepping | (stepping & pstep[2]));

   assign padv_ctrl_o = padv_ctrl;

   assign spr_addr = du_access ? du_addr_i : ctrl_alu_result_i[15:0];
   assign ctrl_mfspr_ack_o = spr_access_ack[spr_group];
   assign ctrl_mtspr_ack_o = spr_access_ack[spr_group];

   // Pipeline flush
   assign pipeline_flush_o = (padv_ctrl & ctrl_op_rfe_i) |
			     (exception_re) |
			     cpu_stall;

   // Flag output
   assign ctrl_flag_o = (!ctrl_flag_clear_i & spr_sr[`OR1K_SPR_SR_F]) |
			ctrl_flag_set_i;

   // Carry output
   assign ctrl_carry_o = (!ctrl_carry_clear_i & spr_sr[`OR1K_SPR_SR_CY]) |
			 ctrl_carry_set_i;

   // Ctrl stage pipeline advance signal is one cycle behind execute stage's
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       padv_ctrl <= 0;
     else
       padv_ctrl <= padv_execute_o;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       execute_waiting_r <= 0;
     else if (!execute_waiting_i)
       execute_waiting_r <= 0;
     else if (decode_valid_i & execute_waiting_i)
       execute_waiting_r <= 1;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       decode_execute_halt <= 0;
     else if (du_restart_from_stall)
       decode_execute_halt <= 0;
     else if (decode_execute_halt & deassert_decode_execute_halt)
       decode_execute_halt <= 0;
     else if ((ctrl_op_rfe_i | exception) & !decode_execute_halt &
	      !exception_taken)
       decode_execute_halt <= 1;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       exception_r <= 0;
     else if (exception_taken | du_restart_from_stall)
       exception_r <= 0;
     else if (exception & !exception_r)
       exception_r <= 1;

   // Signal to indicate that the incoming exception or l.rfe has been taken
   // and we're waiting for it to propagate through the pipeline.
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       exception_taken <= 0;
     else if (exception_taken)
       exception_taken <= 0;
     else if (exception_r & fetch_exception_taken_i)
       exception_taken <= 1;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       last_branch_insn_pc <= 0;
     else if (padv_execute_o & execute_op_branch_i)
       last_branch_insn_pc <= pc_execute_i;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       last_branch_target_pc <= 0;
     else if (padv_execute_o & branch_mispredict_i)
       last_branch_target_pc <= execute_mispredict_target_i;
     else if (padv_decode_o & decode_branch_i)
       last_branch_target_pc <= decode_branch_target_i;

   // Used to gate execute stage's advance signal in the case where a LSU op has
   // finished before the next instruction has been fetched. Typically this
   // occurs when not using icache and doing lots of memory accesses.
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       waiting_for_fetch <= 0;
     else if (fetch_valid_i)
       waiting_for_fetch <= 0;
     else if (!execute_waiting_i & execute_waiting_r & !fetch_valid_i)
       waiting_for_fetch <= 1;


   assign doing_rfe = ((padv_ctrl & ctrl_op_rfe_i) | doing_rfe_r) &
		      !deassert_doing_rfe;

   assign doing_rfe_o = doing_rfe;

   assign deassert_doing_rfe = fetch_exception_taken_i & doing_rfe_r;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       doing_rfe_r <= 0;
     else if (deassert_doing_rfe)
       doing_rfe_r <= 0;
     else if (padv_ctrl)
       doing_rfe_r <= ctrl_op_rfe_i;

   assign spr_sr_o = spr_sr;

   // Supervision register
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_sr <= SPR_SR_RESET_VALUE;
     else if (exception_re)
       begin
	  // Go into supervisor mode, disable interrupts, MMUs
	  spr_sr[`OR1K_SPR_SR_SM  ] <= 1'b1;
	  if (FEATURE_TIMER!="NONE")
	    spr_sr[`OR1K_SPR_SR_TEE ] <= 1'b0;
	  if (FEATURE_PIC!="NONE")
	    spr_sr[`OR1K_SPR_SR_IEE ] <= 1'b0;
	  if (FEATURE_DMMU!="NONE")
	    spr_sr[`OR1K_SPR_SR_DME ] <= 1'b0;
	  if (FEATURE_IMMU!="NONE")
	    spr_sr[`OR1K_SPR_SR_IME ] <= 1'b0;
          if (FEATURE_DSX!="NONE")
	    spr_sr[`OR1K_SPR_SR_DSX ] <= ctrl_delay_slot;
	  if (FEATURE_OVERFLOW!="NONE")
	    spr_sr[`OR1K_SPR_SR_OVE ] <= 1'b0;
       end
     else if ((spr_we & (spr_sr[`OR1K_SPR_SR_SM] & padv_ctrl | du_access)) &&
	      spr_addr==`OR1K_SPR_SR_ADDR)
       begin
	  spr_sr[`OR1K_SPR_SR_SM  ] <= spr_write_dat[`OR1K_SPR_SR_SM  ];

	  spr_sr[`OR1K_SPR_SR_F  ] <= spr_write_dat[`OR1K_SPR_SR_F  ];

	  if (FEATURE_TIMER!="NONE")
	    spr_sr[`OR1K_SPR_SR_TEE ] <= spr_write_dat[`OR1K_SPR_SR_TEE ];

	  if (FEATURE_PIC!="NONE")
	    spr_sr[`OR1K_SPR_SR_IEE ] <= spr_write_dat[`OR1K_SPR_SR_IEE ];

	  if (FEATURE_DATACACHE!="NONE")
	    spr_sr[`OR1K_SPR_SR_DCE ] <= spr_write_dat[`OR1K_SPR_SR_DCE ];

	  if (FEATURE_INSTRUCTIONCACHE!="NONE")
	    spr_sr[`OR1K_SPR_SR_ICE ] <= spr_write_dat[`OR1K_SPR_SR_ICE ];

	  if (FEATURE_DMMU!="NONE")
	    spr_sr[`OR1K_SPR_SR_DME ] <= spr_write_dat[`OR1K_SPR_SR_DME ];

	  if (FEATURE_IMMU!="NONE")
	    spr_sr[`OR1K_SPR_SR_IME ] <= spr_write_dat[`OR1K_SPR_SR_IME ];

	  if (FEATURE_FASTCONTEXTS!="NONE")
	    spr_sr[`OR1K_SPR_SR_CE  ] <= spr_write_dat[`OR1K_SPR_SR_CE  ];

	  spr_sr[`OR1K_SPR_SR_CY  ] <= spr_write_dat[`OR1K_SPR_SR_CY  ];

	  if (FEATURE_OVERFLOW!="NONE") begin
	     spr_sr[`OR1K_SPR_SR_OV  ] <= spr_write_dat[`OR1K_SPR_SR_OV  ];
	     spr_sr[`OR1K_SPR_SR_OVE ] <= spr_write_dat[`OR1K_SPR_SR_OVE ];
	  end

	  if (FEATURE_DSX!="NONE")
	    spr_sr[`OR1K_SPR_SR_DSX ] <= spr_write_dat[`OR1K_SPR_SR_DSX ];

	  spr_sr[`OR1K_SPR_SR_EPH ] <= spr_write_dat[`OR1K_SPR_SR_EPH ];
       end
     else if (padv_ctrl)
       begin
	  spr_sr[`OR1K_SPR_SR_F   ] <= ctrl_flag_set_i ? 1 :
				       ctrl_flag_clear_i ? 0 :
				       spr_sr[`OR1K_SPR_SR_F   ];
	  spr_sr[`OR1K_SPR_SR_CY   ] <= ctrl_carry_set_i ? 1 :
					ctrl_carry_clear_i ? 0 :
					spr_sr[`OR1K_SPR_SR_CY   ];
	  if (FEATURE_OVERFLOW!="NONE")
	    spr_sr[`OR1K_SPR_SR_OV   ] <= ctrl_overflow_set_i ? 1 :
				ctrl_overflow_clear_i ? 0 :
				spr_sr[`OR1K_SPR_SR_OV   ];
	  if (ctrl_op_rfe_i)
	    spr_sr <= spr_esr;
       end


   // Exception SR
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_esr <= SPR_SR_RESET_VALUE;
     else if (exception_re)
       begin
	  spr_esr <= spr_sr;
	  if (FEATURE_OVERFLOW!="NONE")
	    begin
	       if (ctrl_overflow_set_i)
		 spr_esr[`OR1K_SPR_SR_OV] <= 1'b1;
	       else if (ctrl_overflow_clear_i)
		 spr_esr[`OR1K_SPR_SR_OV] <= 1'b0;
	    end
	  if (ctrl_carry_set_i)
	    spr_esr[`OR1K_SPR_SR_CY] <= 1'b1;
	  else if (ctrl_carry_clear_i)
	    spr_esr[`OR1K_SPR_SR_CY] <= 1'b0;
       end
     else if (spr_we & spr_addr==`OR1K_SPR_ESR0_ADDR)
       spr_esr <= spr_write_dat[SPR_SR_WIDTH-1:0];

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       ctrl_bubble <= 0;
     else if (padv_execute_o)
       ctrl_bubble <= execute_bubble_i;

   // Exception PC
   always @(posedge clk)
     if (exception_re) begin
	if (except_ibus_err_i)
	  spr_epcr <= last_branch_insn_pc;
	// Syscall is a special case, we return back to the instruction _after_
	// the syscall instruction, unless the syscall was in a delay slot
	else if (except_syscall_i)
	  spr_epcr <= ctrl_delay_slot ? ctrl_epcr_o : pc_ctrl_i + 4;
	else if (store_buffer_err_i)
	  spr_epcr <= store_buffer_epcr_i;
	else
	  spr_epcr <= ctrl_epcr_o;
     end else if (spr_we && spr_addr==`OR1K_SPR_EPCR0_ADDR) begin
	spr_epcr <= spr_write_dat;
     end

   // Exception Effective Address
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_eear <= {OPTION_OPERAND_WIDTH{1'b0}};
     else if (/*padv_ctrl & exception*/ exception_re)
       begin
	  if (except_ibus_err_i | except_itlb_miss_i | except_ipagefault_i)
	    spr_eear <= pc_ctrl_i;
	  else
	    spr_eear <= ctrl_lsu_adr_i;
       end

   // Track the PC
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_ppc <= OPTION_RESET_PC;
     else if (padv_ctrl)
       spr_ppc <= pc_ctrl_i;

   // Generate the NPC for SPR accesses
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_npc <= OPTION_RESET_PC;
     else if (du_npc_write)
       spr_npc <= du_dat_i;
     else if (du_npc_written)
       spr_npc <= spr_npc;
     else if (stepped_into_rfe)
       spr_npc <= spr_epcr;
     else if (stepped_into_delay_slot)
       spr_npc <= last_branch_target_pc;
     else if (stepped_into_exception)
       spr_npc <= exception_pc_addr;
     else
       spr_npc <= pc_ctrl_i + 4;

   // Exception Vector Address
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_evbar <= {OPTION_OPERAND_WIDTH{1'b0}};
     else if (spr_we && spr_addr==`OR1K_SPR_EVBAR_ADDR)
       spr_evbar <= {spr_write_dat[OPTION_OPERAND_WIDTH-1:13], 13'd0};

   // Remember when we're in a delay slot in execute stage.
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       execute_delay_slot <= 0;
     else if (padv_execute_o)
       execute_delay_slot <= execute_op_branch_i;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       ctrl_delay_slot <= 0;
     else if (padv_execute_o)
       ctrl_delay_slot <= execute_delay_slot;

   mor1kx_cfgrs
     #(.FEATURE_PIC			(FEATURE_PIC),
       .FEATURE_TIMER			(FEATURE_TIMER),
       .OPTION_PIC_TRIGGER		(OPTION_PIC_TRIGGER),
       .FEATURE_DSX			(FEATURE_DSX),
       .FEATURE_FASTCONTEXTS		(FEATURE_FASTCONTEXTS),
       .FEATURE_OVERFLOW		(FEATURE_OVERFLOW),
       .FEATURE_DATACACHE		(FEATURE_DATACACHE),
       .OPTION_DCACHE_BLOCK_WIDTH	(OPTION_DCACHE_BLOCK_WIDTH),
       .OPTION_DCACHE_SET_WIDTH		(OPTION_DCACHE_SET_WIDTH),
       .OPTION_DCACHE_WAYS		(OPTION_DCACHE_WAYS),
       .FEATURE_DMMU			(FEATURE_DMMU),
       .OPTION_DMMU_SET_WIDTH		(OPTION_DMMU_SET_WIDTH),
       .OPTION_DMMU_WAYS		(OPTION_DMMU_WAYS),
       .FEATURE_INSTRUCTIONCACHE	(FEATURE_INSTRUCTIONCACHE),
       .OPTION_ICACHE_BLOCK_WIDTH	(OPTION_ICACHE_BLOCK_WIDTH),
       .OPTION_ICACHE_SET_WIDTH		(OPTION_ICACHE_SET_WIDTH),
       .OPTION_ICACHE_WAYS		(OPTION_ICACHE_WAYS),
       .FEATURE_IMMU			(FEATURE_IMMU),
       .OPTION_IMMU_SET_WIDTH		(OPTION_IMMU_SET_WIDTH),
       .OPTION_IMMU_WAYS		(OPTION_IMMU_WAYS),
       .FEATURE_DEBUGUNIT		(FEATURE_DEBUGUNIT),
       .FEATURE_PERFCOUNTERS		(FEATURE_PERFCOUNTERS),
       .FEATURE_MAC			(FEATURE_MAC),
       .FEATURE_SYSCALL			(FEATURE_SYSCALL),
       .FEATURE_TRAP			(FEATURE_TRAP),
       .FEATURE_RANGE			(FEATURE_RANGE),
       .FEATURE_DELAYSLOT               ("ENABLED"),
       .FEATURE_EVBAR                   ("ENABLED")
       )
   mor1kx_cfgrs
     (/*AUTOINST*/
      // Outputs
      .spr_vr				(spr_vr[31:0]),
      .spr_vr2				(spr_vr2[31:0]),
      .spr_upr				(spr_upr[31:0]),
      .spr_cpucfgr			(spr_cpucfgr[31:0]),
      .spr_dmmucfgr			(spr_dmmucfgr[31:0]),
      .spr_immucfgr			(spr_immucfgr[31:0]),
      .spr_dccfgr			(spr_dccfgr[31:0]),
      .spr_iccfgr			(spr_iccfgr[31:0]),
      .spr_dcfgr			(spr_dcfgr[31:0]),
      .spr_pccfgr			(spr_pccfgr[31:0]),
      .spr_fpcsr			(spr_fpcsr[31:0]),
      .spr_avr				(spr_avr[31:0]));

   /* Implementation-specific registers */
   assign spr_isr[0] = 0;
   assign spr_isr[1] = 0;
   assign spr_isr[2] = 0;
   assign spr_isr[3] = 0;
   assign spr_isr[4] = 0;
   assign spr_isr[5] = 0;
   assign spr_isr[6] = 0;
   assign spr_isr[7] = 0;

   // System group (0) SPR data out
   always @*
     case(spr_addr)
       `OR1K_SPR_VR_ADDR:
	 spr_sys_group_read = spr_vr;
       `OR1K_SPR_VR2_ADDR:
	 spr_sys_group_read = {spr_vr2[31:8], `MOR1KX_PIPEID_CAPPUCCINO};
       `OR1K_SPR_AVR_ADDR:
	 spr_sys_group_read = spr_avr;
       `OR1K_SPR_UPR_ADDR:
	 spr_sys_group_read = spr_upr;
       `OR1K_SPR_CPUCFGR_ADDR:
	 spr_sys_group_read = spr_cpucfgr;
       `OR1K_SPR_DMMUCFGR_ADDR:
	 spr_sys_group_read = spr_dmmucfgr;
       `OR1K_SPR_IMMUCFGR_ADDR:
	 spr_sys_group_read = spr_immucfgr;
       `OR1K_SPR_DCCFGR_ADDR:
	 spr_sys_group_read = spr_dccfgr;
       `OR1K_SPR_ICCFGR_ADDR:
	 spr_sys_group_read = spr_iccfgr;
       `OR1K_SPR_DCFGR_ADDR:
	 spr_sys_group_read = spr_dcfgr;
       `OR1K_SPR_PCCFGR_ADDR:
	 spr_sys_group_read = spr_pccfgr;
       `OR1K_SPR_NPC_ADDR:
	 spr_sys_group_read = spr_npc;
       `OR1K_SPR_SR_ADDR:
	 spr_sys_group_read = {{(OPTION_OPERAND_WIDTH-SPR_SR_WIDTH){1'b0}},
			       spr_sr};

       `OR1K_SPR_PPC_ADDR:
	 spr_sys_group_read = spr_ppc;
       `OR1K_SPR_FPCSR_ADDR:
	 spr_sys_group_read = spr_fpcsr;
       `OR1K_SPR_EPCR0_ADDR:
	 spr_sys_group_read = spr_epcr;
       `OR1K_SPR_EEAR0_ADDR:
	 spr_sys_group_read = spr_eear;
       `OR1K_SPR_ESR0_ADDR:
	 spr_sys_group_read = {{(OPTION_OPERAND_WIDTH-SPR_SR_WIDTH){1'b0}},
			       spr_esr};
       `OR1K_SPR_EVBAR_ADDR:
	 spr_sys_group_read = spr_evbar;
       `OR1K_SPR_ISR0_ADDR:
	 spr_sys_group_read = spr_isr[0];
       `OR1K_SPR_ISR0_ADDR +1:
	 spr_sys_group_read = spr_isr[1];
       `OR1K_SPR_ISR0_ADDR +2:
	 spr_sys_group_read = spr_isr[2];
       `OR1K_SPR_ISR0_ADDR +3:
	 spr_sys_group_read = spr_isr[3];
       `OR1K_SPR_ISR0_ADDR +4:
	 spr_sys_group_read = spr_isr[4];
       `OR1K_SPR_ISR0_ADDR +5:
	 spr_sys_group_read = spr_isr[5];
       `OR1K_SPR_ISR0_ADDR +6:
	 spr_sys_group_read = spr_isr[6];
       `OR1K_SPR_ISR0_ADDR +7:
	 spr_sys_group_read = spr_isr[7];

       default: begin
	  // GPR read
	  if (spr_addr >= `OR1K_SPR_GPR0_ADDR &&
	      spr_addr < (`OR1K_SPR_GPR0_ADDR + 32))
	    spr_sys_group_read = b; // Register file
	  else
	    // Invalid address - read as zero
	    spr_sys_group_read = 0;
       end
     endcase // case (spr_addr)

   /* System group read data MUX in */
   assign spr_internal_read_dat[0] = spr_sys_group_read;
   /* System group ack generation */
   /* TODO - might be delay for register file reads! */
   assign spr_access_ack[0] = 1;


   /* Generate data to the register file for mfspr operations */
   assign mfspr_dat_o = spr_internal_read_dat[spr_addr[14:11]];

   // PIC SPR control
   generate

      if (FEATURE_PIC !="NONE") begin : pic

	 /* mor1kx_pic AUTO_TEMPLATE (
	  .spr_picsr_o		(spr_picsr),
	  .spr_picmr_o		(spr_picmr),
	  .spr_bus_ack		(spr_access_ack[9]),
	  .spr_dat_o		(spr_internal_read_dat[9]),
	  // Inputs
	  .spr_we_i		(spr_we),
	  .spr_addr_i		(spr_addr),
	  .spr_dat_i		(spr_write_dat),
	  );*/
	 mor1kx_pic
	  #(.OPTION_PIC_TRIGGER(OPTION_PIC_TRIGGER))
	 mor1kx_pic
	   (/*AUTOINST*/
	    // Outputs
	    .spr_picmr_o		(spr_picmr),		 // Templated
	    .spr_picsr_o		(spr_picsr),		 // Templated
	    .spr_bus_ack		(spr_access_ack[9]),	 // Templated
	    .spr_dat_o			(spr_internal_read_dat[9]), // Templated
	    // Inputs
	    .clk			(clk),
	    .rst			(rst),
	    .irq_i			(irq_i[31:0]),
	    .spr_we_i			(spr_we),		 // Templated
	    .spr_addr_i			(spr_addr),		 // Templated
	    .spr_dat_i			(spr_write_dat));	 // Templated


	 assign except_pic = (|spr_picsr) & spr_sr[`OR1K_SPR_SR_IEE] &
			     !ctrl_op_mtspr_i & !doing_rfe;
      end
      else begin
	 assign except_pic = 0;
	 assign spr_picsr = 0;
	 assign spr_picmr = 0;
	 assign spr_access_ack[9] = 0;
	 assign spr_internal_read_dat[9] = 0;
      end // else: !if(FEATURE_PIC !="NONE")
   endgenerate


   generate
      if (FEATURE_TIMER!="NONE") begin : tt

	 /* mor1kx_ticktimer AUTO_TEMPLATE (
	  .spr_ttmr_o		(spr_ttmr),
	  .spr_ttcr_o		(spr_ttcr),
	  .spr_bus_ack		(spr_access_ack[10]),
	  .spr_dat_o		(spr_internal_read_dat[10]),
	  // Inputs
	  .spr_we_i		(spr_we),
	  .spr_addr_i		(spr_addr),
	  .spr_dat_i		(spr_write_dat),
	  );*/
	 mor1kx_ticktimer mor1kx_ticktimer
			 (/*AUTOINST*/
			  // Outputs
			  .spr_ttmr_o		(spr_ttmr),	 // Templated
			  .spr_ttcr_o		(spr_ttcr),	 // Templated
			  .spr_bus_ack		(spr_access_ack[10]), // Templated
			  .spr_dat_o		(spr_internal_read_dat[10]), // Templated
			  // Inputs
			  .clk			(clk),
			  .rst			(rst),
			  .spr_we_i		(spr_we),	 // Templated
			  .spr_addr_i		(spr_addr),	 // Templated
			  .spr_dat_i		(spr_write_dat)); // Templated

	 assign except_ticktimer = spr_ttmr[28] & spr_sr[`OR1K_SPR_SR_TEE] &
				   !ctrl_op_mtspr_i & !doing_rfe;

      end // if (FEATURE_TIMER!="NONE")
      else begin
	 assign except_ticktimer = 0;
	 assign spr_ttmr = 0;
	 assign spr_ttcr = 0;
	 assign spr_access_ack[10] = 0;
	 assign spr_internal_read_dat[10] = 0;
      end // else: !if(FEATURE_TIMER!="NONE")
   endgenerate

   /* SPR access control - allow accesses from either the instructions or from
    the debug interface */
   assign spr_read_access = (ctrl_op_mfspr_i | (du_access & !du_we_i));
   assign spr_write_access = (ctrl_op_mtspr_i | (du_access & du_we_i));

   assign spr_write_dat = du_access ? du_dat_i : b;
   assign spr_we = spr_write_access & spr_group_present;
   assign spr_read = spr_read_access & spr_group_present;

   /* A bus out to other units that live outside of the control unit */
   assign spr_bus_addr_o = spr_addr;
   assign spr_bus_we_o = spr_write_access & spr_group_present & spr_bus_access;
   assign spr_bus_stb_o = (spr_read_access | spr_write_access) &
			  spr_group_present & spr_bus_access;
   assign spr_bus_dat_o = spr_write_dat;

   /* Is the SPR in the design? */
   assign spr_group_present = (// System group
			       (spr_addr[15:11]==5'h00) ||
			       // DMMU
			       (spr_addr[15:11]==5'h01 &&
				FEATURE_DMMU!="NONE") ||
			       // IMMU
			       (spr_addr[15:11]==5'h02 &&
				FEATURE_IMMU!="NONE") ||
			       // Data cache
			       (spr_addr[15:11]==5'h03 &&
				FEATURE_DATACACHE!="NONE") ||
			       // Instruction cache
			       (spr_addr[15:11]==5'h04 &&
				FEATURE_INSTRUCTIONCACHE!= "NONE") ||
			       // MAC unit
			       (spr_addr[15:11]==5'h05 &&
				FEATURE_MAC!="NONE") ||
			       // Debug unit
			       (spr_addr[15:11]==5'h06 &&
				FEATURE_DEBUGUNIT!="NONE") ||
			       // Performance counters
			       (spr_addr[15:11]==5'h07 &&
				FEATURE_PERFCOUNTERS!="NONE") ||
			       // Power Management
			       (spr_addr[15:11]==5'h08 &&
				FEATURE_PMU!="NONE") ||
			       // PIC
			       (spr_addr[15:11]==5'h09 &&
				FEATURE_PIC!="NONE") ||
			       // Tick timer
			       (spr_addr[15:11]==5'h0a &&
				FEATURE_TIMER!="NONE") ||
			       // FPU
			       (spr_addr[15:11]==5'h0b &&
				FEATURE_FPU!="NONE")
			       );

   /* Generate a SPR group signal - generate invalid if the group is not
    present in the design */
   assign spr_group = (spr_group_present) ? spr_addr[14:11] : 4'd12;

   /* Default group when a selected one is not present - it reads as zero */
   assign spr_internal_read_dat[12] = 0;
   assign spr_access_ack[12] = 1;

   /* Is a SPR bus access needed, or is the requested SPR in this file? */
   assign spr_bus_access = /* Any of the units we don't have in this file */
			   /* System group */
			   !(spr_addr[15:11]==5'h00 ||
			     /* Debug Group */
			     spr_addr[15:11]==5'h06 ||
			     /* PIC Group */
			     spr_addr[15:11]==5'h09 ||
			     /* Tick Group */
			     spr_addr[15:11]==5'h0a);

   generate
      if (FEATURE_DEBUGUNIT!="NONE") begin : du

	 reg [OPTION_OPERAND_WIDTH-1:0] du_read_dat;

	 reg 				du_ack;
	 reg 				du_stall_r;
	 reg [5:0] 			pstep_r;
	 reg [1:0] 			branch_step;

	 assign du_access = du_stb_i;

	 // Generate ack back to the debug interface bus
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     du_ack <= 0;
	   else if (du_ack)
	     du_ack <= 0;
	   else if (du_stb_i) begin
	      if (!spr_group_present)
		/* Unit doesn't exist, ACK to clear the access, nothing done */
		du_ack <= 1;
	      else if (spr_access_ack[spr_group])
		/* actual access occurred */
		du_ack <= 1;
	   end

	 assign du_ack_o = du_ack;

	 /* Data back to the debug bus */
	 always @(posedge clk)
	   du_read_dat <= spr_internal_read_dat[spr_group];

	 assign du_dat_o = du_read_dat;
	 /* TODO: check into only letting stall go high when we've gracefully
	  completed the instruction currently in the ctrl stage.
	  Why? Potentially an instruction like l.mfspr from an external unit
	  hasn't completed fully, gets interrupted, and it's assumed it's
	  completed, but actually hasn't. */
	 assign cpu_stall = du_stall_i | du_restart_from_stall;

	 /* goes out to the debug interface and comes back 1 cycle later
	  via du_stall_i */
	 assign du_stall_o = stepping & pstep[4];

	 /* Pulse to indicate we're restarting after a stall */
	 assign du_restart_from_stall = du_stall_r & !du_stall_i;

	 /* NPC debug control logic */
	 assign du_npc_write = (du_we_i && du_addr_i==`OR1K_SPR_NPC_ADDR &&
				du_ack_o);

	 /* record if NPC was written while we were stalled.
	  If so, we will use this value for restarting */
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     du_npc_written <= 0;
	   else if (du_restart_from_stall)
	     du_npc_written <= 0;
	   else if (du_npc_write)
	     du_npc_written <= 1;

	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     stepped_into_exception <= 0;
	   else if (du_restart_from_stall)
	     stepped_into_exception <= 0;
	   else if (exception & stepping & (padv_ctrl | ctrl_stage_exceptions))
	     stepped_into_exception <= 1;

	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     stepped_into_rfe <= 0;
	   else if (du_restart_from_stall)
	     stepped_into_rfe <= 0;
	   else if (stepping & padv_ctrl)
	     stepped_into_rfe <= ctrl_op_rfe_i;

	 assign du_restart_pc_o = spr_npc;

	 assign du_restart_o = du_restart_from_stall;

	 /* Indicate when we're stepping */
	 assign stepping = spr_dmr1[`OR1K_SPR_DMR1_ST] &
			   spr_dsr[`OR1K_SPR_DSR_TE];

	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     pstep_r <= 0;
	   else if (du_restart_from_stall & stepping)
	     pstep_r <= 6'h1;
	   else if ((pstep[0] & fetch_valid_i) |
		    /* decode is always single cycle */
		    (pstep[1] & padv_decode_o) |
		    (pstep[2] & (execute_valid_i | ctrl_stage_exceptions)) |
		    /* ctrl stage can deassert execute_valid */
		    (pstep[3] & (execute_valid_i | ctrl_stage_exceptions)) |
		    pstep[4])
	     pstep_r <= {pstep_r[4:0],1'b0};

	 assign pstep = pstep_r;

	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     branch_step <= 0;
	   else if (du_npc_written)
	     branch_step <= 0;
	   else if (stepping & pstep[2])
	     branch_step <= {branch_step[0], decode_branch_i};
	   else if (!stepping & padv_ctrl)
	     branch_step <= {branch_step[0], ctrl_delay_slot};

	 assign stepped_into_delay_slot = branch_step[1] & stepping;

	 /* Signals for waveform debuging */
	 wire [31:0] spr_read_data_group_0;
	 assign spr_read_data_group_0 = spr_internal_read_dat[0];
	 wire [31:0] spr_read_data_group_1;
	 assign spr_read_data_group_1 = spr_internal_read_dat[1];
	 wire [31:0] spr_read_data_group_2;
	 assign spr_read_data_group_2 = spr_internal_read_dat[2];
	 wire [31:0] spr_read_data_group_3;
	 assign spr_read_data_group_3 = spr_internal_read_dat[3];
	 wire [31:0] spr_read_data_group_4;
	 assign spr_read_data_group_4 = spr_internal_read_dat[4];
	 wire [31:0] spr_read_data_group_5;
	 assign spr_read_data_group_5 = spr_internal_read_dat[5];
	 wire [31:0] spr_read_data_group_6;
	 assign spr_read_data_group_6 = spr_internal_read_dat[6];
	 wire [31:0] spr_read_data_group_7;
	 assign spr_read_data_group_7 = spr_internal_read_dat[7];
	 wire [31:0] spr_read_data_group_8;
	 assign spr_read_data_group_8 = spr_internal_read_dat[8];
	 wire [31:0] spr_read_data_group_9;
	 assign spr_read_data_group_9 = spr_internal_read_dat[9];


	 /* always single cycle access */
	 assign spr_access_ack[6] = 1;
	 assign spr_internal_read_dat[6] = (spr_addr==`OR1K_SPR_DMR1_ADDR) ?
					   spr_dmr1 :
					   (spr_addr==`OR1K_SPR_DMR2_ADDR) ?
					   spr_dmr2 :
					   (spr_addr==`OR1K_SPR_DSR_ADDR) ?
					   spr_dsr :
					   (spr_addr==`OR1K_SPR_DRR_ADDR) ?
					   spr_drr : 0;

	 /* Put the incoming stall signal through a register to detect FE */
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     du_stall_r <= 0;
	   else
	     du_stall_r <= du_stall_i;

	 /* DMR1 */
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     spr_dmr1 <= 0;
	   else if (spr_we && spr_addr==`OR1K_SPR_DMR1_ADDR)
	     spr_dmr1[23:0] <= spr_write_dat[23:0];

	 /* DSR */
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     spr_dsr <= 0;
	   else if (spr_we && spr_addr==`OR1K_SPR_DSR_ADDR)
	     spr_dsr[13:0] <= spr_write_dat[13:0];

	 /* DRR */
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     spr_drr <= 0;
	   else if (spr_we && spr_addr==`OR1K_SPR_DRR_ADDR)
	     spr_drr[13:0] <= spr_write_dat[13:0];

      end // block: du
      else
	begin : no_du
	   assign du_access = 0;
	   assign cpu_stall = 0;
	   assign du_stall_o = 0;
	   assign du_ack_o = 0;
	   assign du_restart_o = 0;
	   assign du_restart_pc_o = 0;
	   assign stepping = 0;
	   assign du_npc_write = 0;
	   assign stepped_into_delay_slot = 0;
	   assign du_dat_o = 0;
	   assign du_restart_from_stall = 0;
	   assign spr_access_ack[6] = 1;

	   always @(posedge clk)
	     begin
		spr_dmr1 <= 0;
		spr_dmr2 <= 0;
		spr_dsr <= 0;
		spr_drr <= 0;
		du_npc_written <= 0;
	     end
	end
   endgenerate

   /* Controls to generate ACKs from units that are external to this module */
   generate
      if (FEATURE_DMMU!="NONE") begin : dmmu_ctrl
	 assign spr_access_ack[1] = spr_bus_ack_dmmu_i;
	 assign spr_internal_read_dat[1] = spr_bus_dat_dmmu_i;
      end
      else begin
	 assign spr_access_ack[1] = 1;
	 assign spr_internal_read_dat[1] = 0;
      end
   endgenerate

   generate
      if (FEATURE_IMMU!="NONE") begin : immu_ctrl
	 assign spr_access_ack[2] = spr_bus_ack_immu_i;
	 assign spr_internal_read_dat[2] = spr_bus_dat_immu_i;
      end
      else begin
	 assign spr_access_ack[2] = 1;
	 assign spr_internal_read_dat[2] = 0;
      end
   endgenerate

   generate
      if (FEATURE_DATACACHE!="NONE") begin : datacache_ctrl
	 assign spr_access_ack[3] = spr_bus_ack_dc_i;
	 assign spr_internal_read_dat[3] = spr_bus_dat_dc_i;
      end
      else begin
	 assign spr_access_ack[3] = 1;
	 assign spr_internal_read_dat[3] = 0;
      end
   endgenerate

   generate
      if (FEATURE_INSTRUCTIONCACHE!="NONE") begin : instructioncache_ctrl
	 assign spr_access_ack[4] = spr_bus_ack_ic_i;
	 assign spr_internal_read_dat[4] = spr_bus_dat_ic_i;
      end
      else begin
	 assign spr_access_ack[4] = 1;
	 assign spr_internal_read_dat[4] = 0;
      end
   endgenerate

   generate
      if (FEATURE_MAC!="NONE") begin : mac_ctrl
	 assign spr_access_ack[5] = spr_bus_ack_mac_i;
	 assign spr_internal_read_dat[5] = spr_bus_dat_mac_i;
      end
      else begin
	 assign spr_access_ack[5] = 1;
	 assign spr_internal_read_dat[5] = 0;
      end
   endgenerate

   generate
      if (FEATURE_PERFCOUNTERS!="NONE") begin : perfcounters_ctrl
	 assign spr_access_ack[7] = spr_bus_ack_pcu_i;
	 assign spr_internal_read_dat[7] = spr_bus_dat_pcu_i;
      end
      else begin
	 assign spr_access_ack[7] = 1;
	 assign spr_internal_read_dat[7] = 0;
      end
   endgenerate

   generate
      if (FEATURE_PMU!="NONE") begin : pmu_ctrl
	 assign spr_access_ack[8] = spr_bus_ack_pmu_i;
	 assign spr_internal_read_dat[8] = spr_bus_dat_pcu_i;
      end
      else begin
	 assign spr_access_ack[8] = 1;
	 assign spr_internal_read_dat[8] = 0;
      end
   endgenerate

   generate
      if (FEATURE_FPU!="NONE") begin : fpu_ctrl
	 assign spr_access_ack[11] = spr_bus_ack_fpu_i;
	 assign spr_internal_read_dat[11] = spr_bus_dat_fpu_i;
      end
      else begin
	 assign spr_access_ack[11] = 1;
	 assign spr_internal_read_dat[11] = 0;
      end
   endgenerate

endmodule // mor1kx_ctrl_cappuccino
