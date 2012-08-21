/* ****************************************************************************
  This Source Code Form is subject to the terms of the 
  Open Hardware Description License, v. 1.0. If a copy 
  of the OHDL was not distributed with this file, You 
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: mor1k control unit
   
  inputs from execute stage
  
  generate pipeline controls
  
  manage SPRs
  
  issue addresses for exceptions to fetch stage
  control branches going to fetch stage
  
  contains tick timer
  
  contains PIC logic
  
  l.mfspr implemented as follows:
  We receieve an indication from the execute stage if it has a l.mfspr 
  instruction. We take note of this and it causes a 1-cycle stall of
  the fetch and decode stages. We still issue the asserted padv_execute so
  we get the result from the ALU which will be the address of the SPR to write
  into the register file. On the next cycle, with the SPR address known, the
  data is output to the RF and the ctrl_mfspr_we_o is asserted ensuring this 
  value is written into the RF. As we introduced a delay in the fetch/decode
  logic, this should not clash with the next instruction to be executed.
   
  Copyright (C) 2012 Authors
 
  Author(s): Julius Baxter <juliusbaxter@gmail.com>
 
***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_ctrl_cappuccino
  (/*AUTOARG*/
   // Outputs
   mfspr_dat_o, ctrl_mfspr_we_o, ctrl_flag_o, ctrl_branch_exception_o,
   ctrl_branch_except_pc_o, pipeline_flush_o, padv_fetch_o,
   padv_decode_o, padv_execute_o, du_dat_o, du_ack_o, du_stall_o,
   du_restart_pc_o, du_restart_o, spr_bus_addr_o, spr_bus_we_o,
   spr_bus_stb_o, spr_bus_dat_o, spr_sr_o,
   // Inputs
   clk, rst, ctrl_alu_result_i, ctrl_rfb_i, ctrl_flag_set_i,
   ctrl_flag_clear_i, pc_ctrl_i, ctrl_opc_insn_i, ctrl_branch_occur_i,
   ctrl_branch_target_i, pc_execute_i, execute_opc_insn_i,
   except_ibus_err_i, except_ibus_align_i, except_illegal_i,
   except_syscall_i, except_dbus_i, except_trap_i, except_align_i,
   fetch_valid_i, decode_valid_i, execute_valid_i, execute_waiting_i,
   fetch_branch_taken_i, irq_i, du_addr_i, du_stb_i, du_dat_i,
   du_we_i, du_stall_i, spr_bus_dat_dc_i, spr_bus_ack_dc_i,
   spr_bus_dat_ic_i, spr_bus_ack_ic_i, spr_bus_dat_dmmu_i,
   spr_bus_ack_dmmu_i, spr_bus_dat_immu_i, spr_bus_ack_immu_i,
   spr_bus_dat_mac_i, spr_bus_ack_mac_i, spr_bus_dat_pmu_i,
   spr_bus_ack_pmu_i, spr_bus_dat_pcu_i, spr_bus_ack_pcu_i,
   spr_bus_dat_fpu_i, spr_bus_ack_fpu_i
   );

   parameter OPTION_OPERAND_WIDTH = 32;
   parameter OPTION_RESET_PC = {{(OPTION_OPERAND_WIDTH-13){1'b0}},
				`OR1K_RESET_VECTOR,8'd0};

   parameter FEATURE_SYSCALL = "ENABLED";
   parameter FEATURE_TRAP = "ENABLED";
   parameter FEATURE_RANGE = "ENABLED";

   parameter FEATURE_DATACACHE = "NONE";
   parameter OPTION_DCACHE_BLOCK_WIDTH = 5;
   parameter OPTION_DCACHE_SET_WIDTH = 9;
   parameter OPTION_DCACHE_WAYS = 2;
   parameter FEATURE_DMMU = "NONE";
   parameter FEATURE_INSTRUCTIONCACHE = "NONE";
   parameter OPTION_ICACHE_BLOCK_WIDTH = 5;
   parameter OPTION_ICACHE_SET_WIDTH = 9;
   parameter OPTION_ICACHE_WAYS = 2;
   parameter FEATURE_IMMU = "NONE";
   parameter FEATURE_PIC = "ENABLED";
   parameter FEATURE_TIMER = "ENABLED";
   parameter FEATURE_DEBUGUNIT = "NONE";
   parameter FEATURE_PERFCOUNTERS = "NONE";
   parameter FEATURE_PMU = "NONE";
   parameter FEATURE_MAC = "NONE";
   parameter FEATURE_FPU = "NONE";   

   parameter OPTION_PIC_TRIGGER = "EDGE";

   parameter FEATURE_DSX ="NONE";
   parameter FEATURE_FASTCONTEXTS = "NONE";
   parameter FEATURE_OVERFLOW = "NONE";

   parameter SPR_SR_WIDTH = 16;
   parameter SPR_SR_RESET_VALUE = 16'h8001;

   input clk, rst;

   // ALU result - either jump target, SPR address
   input [OPTION_OPERAND_WIDTH-1:0] ctrl_alu_result_i;
   
   // Operand B from RF might be jump address, might be value for SPR
   input [OPTION_OPERAND_WIDTH-1:0] ctrl_rfb_i;
   
   input 			    ctrl_flag_set_i, ctrl_flag_clear_i;
   
   input [OPTION_OPERAND_WIDTH-1:0] pc_ctrl_i;

   input [`OR1K_OPCODE_WIDTH-1:0]   ctrl_opc_insn_i;
   
   // Indicate if branch will be taken based on instruction currently in
   // execute stage. Combinatorially generated, uses signals from both
   // execute and ctrl stage.
   input 			    ctrl_branch_occur_i;
   input [OPTION_OPERAND_WIDTH-1:0] ctrl_branch_target_i;

   // PC of execute stage (NPC)
   input [OPTION_OPERAND_WIDTH-1:0] pc_execute_i;
   // Opcode of execute stage instruction
   input [`OR1K_OPCODE_WIDTH-1:0]   execute_opc_insn_i;
   
   // Exception inputs, registered on output of execute stage
   input 			    except_ibus_err_i, except_ibus_align_i, 
				    except_illegal_i, 
				    except_syscall_i, except_dbus_i, 
				    except_trap_i, except_align_i;
   
   // Inputs from two units that can stall proceedings
   input 			    fetch_valid_i,   decode_valid_i,
				    execute_valid_i;
   input 			    execute_waiting_i;
   
   input 			    fetch_branch_taken_i;

   // External IRQ lines in
   input [31:0] 		    irq_i;
   
   // SPR data out
   output [OPTION_OPERAND_WIDTH-1:0] mfspr_dat_o;
   
   // WE to RF for l.mfspr
   output 			     ctrl_mfspr_we_o;
   
   // Flag out to branch control, combinatorial
   output 			     ctrl_flag_o;
   
   // Branch indicator from control unit (l.rfe/exception)
   output 			     ctrl_branch_exception_o;
   // PC out to fetch stage for l.rfe, exceptions
   output [OPTION_OPERAND_WIDTH-1:0] ctrl_branch_except_pc_o;
   
   // Clear instructions from decode and fetch stage
   output 			     pipeline_flush_o;
   
   output 			     padv_fetch_o;
   output 			     padv_decode_o;
   output 			     padv_execute_o;
   
   // Debug bus
   input [15:0] 		     du_addr_i;
   input 			     du_stb_i;
   input [OPTION_OPERAND_WIDTH-1:0]  du_dat_i;
   input 			     du_we_i;
   output [OPTION_OPERAND_WIDTH-1:0] du_dat_o;
   output 			     du_ack_o;
   // Stall control from debug interface
   input 			     du_stall_i;
   output 			     du_stall_o;
   output [OPTION_OPERAND_WIDTH-1:0] du_restart_pc_o;
   output 			     du_restart_o;
   
   // SPR accesses to external units (cache, mmu, etc.)
   output [15:0] 		     spr_bus_addr_o;
   output 			     spr_bus_we_o;
   output 			     spr_bus_stb_o;
   output [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o;
   input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_dc_i;
   input 			     spr_bus_ack_dc_i;   
   input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_ic_i;
   input 			     spr_bus_ack_ic_i;   
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
   output [15:0] 	     spr_sr_o;
   
   // Internal signals
   reg [SPR_SR_WIDTH-1:0] 	     spr_sr;
   reg [SPR_SR_WIDTH-1:0] 	     spr_esr;
   reg [OPTION_OPERAND_WIDTH-1:0]    spr_epcr;
   reg [OPTION_OPERAND_WIDTH-1:0]    spr_eear;
   reg [OPTION_OPERAND_WIDTH-1:0]    spr_evba;
   
   // Programmable Interrupt Control SPRs
   reg [31:0] 			     spr_picmr;
   reg [31:0] 			     spr_picsr;
   
   // Tick Timer SPRs
   reg [31:0] 			     spr_ttmr;
   reg [31:0] 			     spr_ttcr;
   
   reg [OPTION_OPERAND_WIDTH-1:0]    spr_ppc;
   wire [OPTION_OPERAND_WIDTH-1:0]   spr_npc;
   reg 				     execute_delay_slot;
   reg 				     ctrl_delay_slot;
   
   reg 				     mfspr_delay, mfspr_done;
   
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

   wire 			     execute_stage_exceptions;
   wire 			     decode_stage_exceptions;

   wire 			     exception_re;

   wire [31:0] 			     irq_unmasked;

   wire 			     except_ticktimer;
   wire 			     except_pic;
   
   
   wire [15:0] 			     spr_addr;
   
   wire 			     op_mtspr;
   wire 			     op_mfspr;
   wire 			     op_rfe;

   wire [OPTION_OPERAND_WIDTH-1:0]   b;

   wire 			     execute_op_mfspr;
   wire 			     wait_mfspr;

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
   wire [3:0] 			     pstep;
   wire 			     stepping;
   wire 			     stepped_into_delay_slot;
   wire 			     du_npc_write;
   reg 				     du_npc_written;
   reg [OPTION_OPERAND_WIDTH-1:0]    du_spr_npc;
   
   /* Wires for SPR management */
   wire 			     spr_group_present;
   wire [3:0] 			     spr_group;
   wire 			     spr_we;
      wire 			     spr_read;
   wire [OPTION_OPERAND_WIDTH-1:0]   spr_write_dat;
   wire [11:0] 			     spr_access_ack;
   wire [31:0] 			     spr_internal_read_dat [0:12];
   wire 			     spr_read_access;
   wire 			     spr_write_access;
   wire 			     spr_bus_access;
   reg [OPTION_OPERAND_WIDTH-1:0]    spr_sys_group_read;

   assign  b = ctrl_rfb_i;

   assign ctrl_branch_exception_o = (exception_r | (op_rfe | doing_rfe)) & 
				    !exception_taken;
   assign exception_pending = (except_ibus_err_i | except_ibus_align_i | 
		       except_illegal_i | except_syscall_i |
		       except_dbus_i | except_align_i | except_ticktimer |
			       except_pic | except_trap_i );
      
   assign exception = exception_pending & padv_ctrl;

   assign execute_stage_exceptions = except_dbus_i | except_align_i;
   assign decode_stage_exceptions = except_trap_i | except_illegal_i;

   assign exception_re = exception & !exception_r & !exception_taken;
   
   assign deassert_decode_execute_halt = fetch_branch_taken_i &
					 decode_execute_halt;
   
   assign ctrl_branch_except_pc_o = (op_rfe | doing_rfe) ? spr_epcr : 
				    exception_pc_addr;

   always @(posedge clk)
     if (exception & !exception_r)
       casez(
	     {except_ibus_err_i,
	      except_illegal_i,
	      except_align_i,
	      except_ibus_align_i,
	      except_syscall_i,
	      except_trap_i,
	      except_dbus_i,
	      except_pic,
	      except_ticktimer
	      }
	     )
	 9'b1????????:
	   exception_pc_addr <= spr_evba |
				{19'd0,`OR1K_BERR_VECTOR,8'd0};
	 9'b01???????:
	   exception_pc_addr <= spr_evba |
				{19'd0,`OR1K_ILLEGAL_VECTOR,8'd0};
	 9'b001??????,
	   9'b0001?????:
	     exception_pc_addr <= spr_evba |
				  {19'd0,`OR1K_ALIGN_VECTOR,8'd0};
	 9'b00001????:
	   exception_pc_addr <= spr_evba |
				{19'd0,`OR1K_SYSCALL_VECTOR,8'd0};
	 9'b000001???:
	   exception_pc_addr <= spr_evba |
				{19'd0,`OR1K_TRAP_VECTOR,8'd0};
	 9'b0000001??:
	   exception_pc_addr <= spr_evba |
				{19'd0,`OR1K_BERR_VECTOR,8'd0};
	 9'b00000001?:
	   exception_pc_addr <= spr_evba |
				{19'd0,`OR1K_INT_VECTOR,8'd0};
	 //9'b000000001:
	 default:
	   exception_pc_addr <= spr_evba |
				{19'd0,`OR1K_TT_VECTOR,8'd0};
       endcase // casex (...
   
   assign op_mtspr = ctrl_opc_insn_i==`OR1K_OPCODE_MTSPR;
   assign op_mfspr = ctrl_opc_insn_i==`OR1K_OPCODE_MFSPR;
   assign execute_op_mfspr = execute_opc_insn_i==`OR1K_OPCODE_MFSPR;
   assign op_rfe = ctrl_opc_insn_i==`OR1K_OPCODE_RFE;

   assign wait_mfspr = execute_op_mfspr & !mfspr_delay & !mfspr_done;

   assign padv_fetch_o = !execute_waiting_i & !wait_mfspr & !cpu_stall
			 & (!stepping | (stepping & pstep[0] & !fetch_valid_i));

   assign padv_decode_o = fetch_valid_i & !execute_waiting_i & 
			  !wait_mfspr & !decode_execute_halt & !cpu_stall
			  & (!stepping | (stepping & pstep[1]));
   
   assign padv_execute_o = ((decode_valid_i & !execute_waiting_i &
			     /* Stop fetch before exception branch continuing */
			     !(exception_r & fetch_branch_taken_i)) |
			    (!execute_waiting_i & execute_waiting_r & 
			     fetch_valid_i) |
			    // Case where execute became ready before fetch
			    // after delay in execute stage
			    (waiting_for_fetch & fetch_valid_i)) &
			   // Not exceptions occurring
			   !decode_execute_halt & !exception_re & !op_rfe
			   & !cpu_stall & (!stepping | (stepping & pstep[2]));
   
   assign spr_addr = du_access ? du_addr_i : ctrl_alu_result_i[15:0];
   assign ctrl_mfspr_we_o = mfspr_delay;

   // Pipeline flush
   assign pipeline_flush_o = (padv_ctrl & op_rfe) |
			     (exception_re) |
			     cpu_stall;

   // Flag output
   assign ctrl_flag_o = (!ctrl_flag_clear_i & spr_sr[`OR1K_SPR_SR_F]) |
			ctrl_flag_set_i;

   // Ctrl stage pipeline advance signal is one cycle behind execute stage's
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       padv_ctrl <= 0;
     else
       padv_ctrl <= padv_execute_o;
   
   // Generate delay if necessary, when we have mtspr followed by mfspr
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       mfspr_delay <= 0;
     else if (mfspr_delay)
       mfspr_delay <= 0;
     else if (execute_op_mfspr & !mfspr_done)
       mfspr_delay <= 1;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       mfspr_done <= 0;
     else if (padv_decode_o )
       mfspr_done <= 0;
   /* TODO - wait on bus access if we need to */
     else if (mfspr_delay)
       mfspr_done <= 1;

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
     else if ((op_rfe | exception) & !decode_execute_halt & !exception_taken)
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
     else if (exception_r & fetch_branch_taken_i)
       exception_taken <= 1;
   
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       last_branch_insn_pc <= 0;
     else if (padv_execute_o & ctrl_branch_occur_i)
       last_branch_insn_pc <= pc_execute_i;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       last_branch_target_pc <= 0;
     else if (padv_execute_o & ctrl_branch_occur_i)
       last_branch_target_pc <= ctrl_branch_target_i;

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


   assign doing_rfe = ((padv_ctrl & op_rfe) | doing_rfe_r) & 
		      !deassert_doing_rfe;

   assign deassert_doing_rfe = fetch_branch_taken_i & doing_rfe_r;
   
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       doing_rfe_r <= 0;
     else if (deassert_doing_rfe)
       doing_rfe_r <= 0;
     else if (padv_ctrl)
       doing_rfe_r <= op_rfe;
   
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
       end
     else if (padv_ctrl)
       begin
	  if (ctrl_flag_set_i)
	    spr_sr[`OR1K_SPR_SR_F   ] <= 1'b1;
	  else if (ctrl_flag_clear_i)
	    spr_sr[`OR1K_SPR_SR_F   ] <= 1'b0;
	  else if ((spr_we & (spr_sr[`OR1K_SPR_SR_SM] | du_access)) && 
		   spr_addr==`OR1K_SPR_SR_ADDR)
	    begin
	       spr_sr[`OR1K_SPR_SR_SM  ] <= spr_write_dat[`OR1K_SPR_SR_SM  ];

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
	  else if (op_rfe)
	    spr_sr <= spr_esr;
       end // if (padv_ctrl)
   
   // Exception SR
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_esr <= SPR_SR_RESET_VALUE;
     else if (/*padv_ctrl & exception*/ exception_re)
       begin
	  spr_esr <= spr_sr;
	  /* 
	   A bit odd, but if we had a l.sf instruction on an exception rising
	   edge, EPCR will point to the insn past the l.sf but the flag will
	   not have been saved to the SR properly. So we must put it in here
	   so it can be restored correctly.
	   */
	  if (padv_ctrl)
	    if (ctrl_flag_set_i)
	      spr_esr[`OR1K_SPR_SR_F   ] <= 1'b1;
	    else if (ctrl_flag_clear_i)
	      spr_esr[`OR1K_SPR_SR_F   ] <= 1'b0;
       end
     else if (spr_we & spr_addr==`OR1K_SPR_ESR0_ADDR)
       spr_esr <= spr_write_dat[SPR_SR_WIDTH-1:0];
   
   // Exception PC
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_epcr <= OPTION_RESET_PC;
     else if (/*padv_ctrl & exception*/ exception_re)
       begin
	  if (except_ibus_err_i)
	    spr_epcr <= last_branch_insn_pc;
	  else if (except_syscall_i | except_ticktimer | except_pic)
	    // TODO - eliminate this adder by getting PC from pipeline stages
	    spr_epcr <= ctrl_delay_slot ? last_branch_target_pc :
			/* 
			execute_delay_slot ? last_branch_insn_pc :
			 */
			pc_ctrl_i + 4;
	  else if (execute_stage_exceptions | decode_stage_exceptions)
	    spr_epcr <= ctrl_delay_slot ? spr_ppc : pc_ctrl_i;
	  else
	    spr_epcr <= execute_delay_slot ? spr_ppc : pc_ctrl_i;
       end
     else if (spr_we && spr_addr==`OR1K_SPR_EPCR0_ADDR)
       spr_epcr <= spr_write_dat;
   
   // Exception Effective Address 
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_eear <= {OPTION_OPERAND_WIDTH{1'b0}};
     else if (/*padv_ctrl & exception*/ exception_re)
       begin
	  if (except_ibus_err_i)
	    spr_eear <= pc_ctrl_i;
	  else
	    spr_eear <= ctrl_alu_result_i;
       end

   // Track the PC
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_ppc <= OPTION_RESET_PC;
     else if (padv_ctrl)
       spr_ppc <= pc_ctrl_i;

   // assign the NPC for SPR accesses
   assign spr_npc = du_npc_written ? du_spr_npc : pc_ctrl_i;

   // Exception Vector Address
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_evba <= {OPTION_OPERAND_WIDTH{1'b0}};
     else if (spr_we && spr_addr==`OR1K_SPR_EVBA_ADDR)
       spr_evba <= {spr_write_dat[OPTION_OPERAND_WIDTH-1:13], 13'd0};

   // Remember when we're in a delay slot in execute stage.
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       execute_delay_slot <= 0;
   // Considerations:
   // Have to wait until it looks like the exception is starting to progress
   // through the pipeline.
   // A bit tricky, because in a delay slot, and we're a LSU op, we must
   // wait, and it's likely the instruction fetch for the branch target we
   // won't be going to just yet will pulse and we have to make sure don't
   // drop this signal until the LSU op as finished, and the fetch has been
   // done.
   // In the case of a l.trap or illegal instruction in delay slot, it will
   // propegate through the execute stage in a single cycle, so in that case
   // we are
   // can proceed.
     else if (execute_delay_slot & padv_execute_o)
       execute_delay_slot <= 0;
   // Register if a branch occurred when we're about to clock through
   // the next inputs to the execute stage.
     else if (padv_decode_o)
       execute_delay_slot <= ctrl_branch_occur_i & !ctrl_delay_slot & 
			     !(doing_rfe | op_rfe);

   
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       ctrl_delay_slot <= 0;
     else if (padv_execute_o)
       ctrl_delay_slot <= execute_delay_slot;
   
   wire [31:0] spr_vr;
   wire [31:0] spr_upr;
   wire [31:0] spr_cpucfgr;
   wire [31:0] spr_dmmucfgr;
   wire [31:0] spr_immucfgr;
   wire [31:0] spr_dccfgr;
   wire [31:0] spr_iccfgr;
   wire [31:0] spr_dcfgr;
   wire [31:0] spr_pccfgr;
   wire [31:0] spr_fpcsr;

   assign spr_vr[`OR1K_SPR_VR_REV] = 0;
   assign spr_vr[`OR1K_SPR_VR_RESERVED] = 0;
   assign spr_vr[`OR1K_SPR_VR_CFG] = 0;
   assign spr_vr[`OR1K_SPR_VR_VER] = 0;
   
   assign spr_upr[`OR1K_SPR_UPR_UP] = 1;
   assign spr_upr[`OR1K_SPR_UPR_DCP] = (FEATURE_DATACACHE!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_ICP] = (FEATURE_INSTRUCTIONCACHE!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_DMP] = (FEATURE_DMMU!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_IMP] = (FEATURE_IMMU!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_MP] = (FEATURE_MAC!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_DUP] = (FEATURE_DEBUGUNIT!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_PCUP] = (FEATURE_PERFCOUNTERS!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_PICP] = (FEATURE_PIC!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_PMP] = (FEATURE_PMU!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_TTP] = (FEATURE_TIMER!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_RESERVED] = 0;
   assign spr_upr[`OR1K_SPR_UPR_CUP] = 0;

   assign spr_cpucfgr[`OR1K_SPR_CPUCFGR_NSGF] = 0;
   assign spr_cpucfgr[`OR1K_SPR_CPUCFGR_CFG] = 0;
   assign spr_cpucfgr[`OR1K_SPR_CPUCFGR_OB32S] = 1;
   assign spr_cpucfgr[`OR1K_SPR_CPUCFGR_OB64S] = 0;
   assign spr_cpucfgr[`OR1K_SPR_CPUCFGR_OF32S] = 0;
   assign spr_cpucfgr[`OR1K_SPR_CPUCFGR_OF64S] = 0;
   assign spr_cpucfgr[`OR1K_SPR_CPUCFGR_OV64S] = 0;
   assign spr_cpucfgr[`OR1K_SPR_CPUCFGR_RESERVED] = 0;

   assign spr_dmmucfgr = 0;
   assign spr_immucfgr = 0;

   /* Data Cache Configuration register */
   /* Reserved */
   assign spr_dccfgr[31:15] = 0;
   /* Cache Block Write-Back Register Implemented */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_CBWBRI] = 0;
   /* Cache Block Flush Register Implemented */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_CBFRI] = (FEATURE_DATACACHE!="NONE");
   /* Cache Block Lock Register Implemented */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_CBLRI] = 0;
   /* Cache Block Prefetch Register Implemented */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_CBPRI] = 0;
   /* Cache Block Invalidate Register Implemented */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_CBIRI] = (FEATURE_DATACACHE!="NONE");
   /* Cache Control Register Implemented */
   assign spr_iccfgr[`OR1K_SPR_DCCFGR_CCRI] = 0;
   /* Cache Write Strategy (0 = write-through, 1 = write-back) */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_CWS] = 0;
   /* Cache Block Size (0 = 16 bytes, 1 = 32 bytes) */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_CBS] = (FEATURE_DATACACHE!="NONE") ?
					     (OPTION_DCACHE_BLOCK_WIDTH == 5 ? 1 : 0) :  0;
  /* Number of Cache Sets */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_NCS] = (FEATURE_DATACACHE!="NONE") ?
					     OPTION_DCACHE_SET_WIDTH : 0;
   /* Number of Cache Ways */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_NCW] = (FEATURE_DATACACHE!="NONE") ?
					     (OPTION_DCACHE_WAYS == 1) ? 3'd0 :
					     (OPTION_DCACHE_WAYS == 2) ? 3'd1 :
					     (OPTION_DCACHE_WAYS == 4) ? 3'd2 :
					     (OPTION_DCACHE_WAYS == 8) ? 3'd3 :
					     (OPTION_DCACHE_WAYS == 16) ? 3'd4 :
					     (OPTION_DCACHE_WAYS == 32) ? 3'd5 :
					     3'd0 : 3'd0;

   /* Instruction Cache Configuration register */
   /* Reserved */
   assign spr_iccfgr[31:13] = 0;
   assign spr_iccfgr[8] = 0;
   /* Cache Block Lock Register Implemented */
   assign spr_iccfgr[`OR1K_SPR_ICCFGR_CBLRI] = 0;
   /* Cache Block Prefetch Register Implemented */
   assign spr_iccfgr[`OR1K_SPR_ICCFGR_CBPRI] = 0;
   /* Cache Block Invalidate Register Implemented */
   assign spr_iccfgr[`OR1K_SPR_ICCFGR_CBIRI] = (FEATURE_INSTRUCTIONCACHE!="NONE");
   /* Cache Control Register Implemented */
   assign spr_iccfgr[`OR1K_SPR_ICCFGR_CCRI] = 0;
   /* Cache Block Size (0 = 16 bytes, 1 = 32 bytes) */
   assign spr_iccfgr[`OR1K_SPR_ICCFGR_CBS] = (FEATURE_INSTRUCTIONCACHE!="NONE") ?
					     (OPTION_ICACHE_BLOCK_WIDTH == 5 ? 1 : 0) :  0;
  /* Number of Cache Sets */
   assign spr_iccfgr[`OR1K_SPR_ICCFGR_NCS] = (FEATURE_INSTRUCTIONCACHE!="NONE") ?
					     OPTION_ICACHE_SET_WIDTH : 0;
   /* Number of Cache Ways */
   assign spr_iccfgr[`OR1K_SPR_ICCFGR_NCW] = (FEATURE_INSTRUCTIONCACHE!="NONE") ?
					     (OPTION_ICACHE_WAYS == 1) ? 3'd0 :
					     (OPTION_ICACHE_WAYS == 2) ? 3'd1 :
					     (OPTION_ICACHE_WAYS == 4) ? 3'd2 :
					     (OPTION_ICACHE_WAYS == 8) ? 3'd3 :
					     (OPTION_ICACHE_WAYS == 16) ? 3'd4 :
					     (OPTION_ICACHE_WAYS == 32) ? 3'd5 :
					     3'd0 : 3'd0;
   

   assign spr_dcfgr = 0;
   assign spr_pccfgr = 0;   
   assign spr_fpcsr = 0;

   
   // System group (0) SPR data out
   always @*
     case(spr_addr)
       `OR1K_SPR_VR_ADDR:
	 spr_sys_group_read = spr_vr;
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
       `OR1K_SPR_EVBA_ADDR:
	 spr_sys_group_read = spr_evba;
       default: begin
	  /* GPR read */
	  if (spr_addr >= `OR1K_SPR_GPR0_ADDR &&
	      spr_addr <= (`OR1K_SPR_GPR0_ADDR + 32))
	    spr_sys_group_read = b; /* Register file */
	  else
	    /* Invalid address - read as zero*/
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
      genvar   irqline;
      if (FEATURE_PIC !="NONE") begin : pic
	 
	 if (OPTION_PIC_TRIGGER=="EDGE") begin
	    for(irqline=0;irqline<32;irqline=irqline+1)
	      begin: picgenerate
		 // PIC status register
		 always @(posedge clk `OR_ASYNC_RST)
		   if (rst)
		     spr_picsr[irqline] <= 0;
		   // Clear
		   else if (spr_we & spr_addr==`OR1K_SPR_PICSR_ADDR)
		     spr_picsr[irqline] <= spr_write_dat[irqline] ? 0 : 
					      spr_picsr[irqline];
		   // Set
		   else if (!spr_picsr[irqline] & irq_unmasked[irqline])
		     spr_picsr[irqline] <= 1;
	      end // block: picgenerate
	    
	 end // if (OPTION_PIC_TRIGGER=="EDGE")
	 else if (OPTION_PIC_TRIGGER=="LEVEL") begin
	    for(irqline=0;irqline<32;irqline=irqline+1)
	      begin: picsrlevelgenerate
		 
		 // PIC status register
		 always @(posedge clk `OR_ASYNC_RST)
		   spr_picsr[irqline] <= irq_unmasked[irqline];
	      end
	    
	 end // if (OPTION_PIC_TRIGGER=="LEVEL")
	 else if (OPTION_PIC_TRIGGER=="LATCHED_LEVEL") begin
	    for(irqline=0;irqline<32;irqline=irqline+1)
	      begin: piclatchedlevelgenerate
		 // PIC status register
		 always @(posedge clk `OR_ASYNC_RST)
		   if (rst)
		     spr_picsr[irqline] <= 0;
		   else if (spr_we & spr_addr==`OR1K_SPR_PICSR_ADDR)
		     spr_picsr[irqline] <= irq_unmasked[irqline] | 
					      spr_write_dat[irqline];
		   else 
		     spr_picsr[irqline] <= spr_picsr[irqline] | 
					   irq_unmasked[irqline];
	      end // block: picgenerate
	    
	 end // if (OPTION_PIC_TRIGGER=="EDGE")	 
	 else begin
	    initial begin
	       $display("Error - invalid PIC level detection option %s",
			OPTION_PIC_TRIGGER);
	       $finish;
	    end
	 end // else: !if(OPTION_PIC_TRIGGER=="LEVEL")

	 // PIC (un)mask register
	 // Bottom two IRQs permanently unmasked
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     spr_picmr <= {30'd0, 2'b11};
	   else if (spr_we & spr_addr==`OR1K_SPR_PICMR_ADDR)
	     spr_picmr <= {spr_write_dat[31:2], 2'b11};
	 
	 
	 assign irq_unmasked = spr_picmr & irq_i;
	 
	 assign except_pic = (|spr_picsr) & spr_sr[`OR1K_SPR_SR_IEE] & 
			     !op_mtspr & !doing_rfe &
			     // Stops back-to-back branch addresses going to 
			     // fetch stage
			     !ctrl_branch_occur_i &
			     // Stops issues with PC when branching
			     !execute_delay_slot;

	 /* always single cycle access */
	 assign spr_access_ack[9] = 1;
	 assign spr_internal_read_dat[9] =  (spr_addr==`OR1K_SPR_PICSR_ADDR) ?
					    spr_picsr :
					    (spr_addr==`OR1K_SPR_PICMR_ADDR) ?
					    spr_picmr : 0;
	 
      end
      else begin
	 assign except_pic = 0;
	 
	 always @(posedge clk) begin
	    spr_picsr = 0;
	    spr_picmr = 0;
	 end

	 assign spr_access_ack[9] = 0;
	 
      end // else: !if(FEATURE_PIC !="NONE")
   endgenerate
   
   
   generate
      if (FEATURE_TIMER!="NONE") begin : tt
	 
	 // Timer SPR control   
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     spr_ttmr <= 0;
	   else if (spr_we && spr_addr==`OR1K_SPR_TTMR_ADDR)
	     spr_ttmr <= spr_write_dat[31:0];
	   else if ((spr_ttmr[27:0]==spr_ttcr[27:0]) & spr_ttmr[29])
	     spr_ttmr[28] <= 1; // Generate interrupt
	 
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     spr_ttcr <= 0;
	   else if (spr_we && spr_addr==`OR1K_SPR_TTCR_ADDR)
	     spr_ttcr <= spr_write_dat[31:0];
	   else if (spr_ttmr[27:0]==spr_ttcr[27:0])
	     begin
		case(spr_ttmr[31:30])
		  2'b01: // Restart
		    spr_ttcr <= 0;
		  2'b11: // Continuous
		    spr_ttcr <= spr_ttcr + 1;
		  default: // Stop, or disabled
		    spr_ttcr <= spr_ttcr;
		endcase // case (spr_ttmr[31:30])
	     end // if (spr_ttmr[27:0]==spr_ttcr[27:0])
	   else if (|spr_ttmr[31:30])
	     spr_ttcr <= spr_ttcr + 1;

	 assign except_ticktimer = spr_ttmr[28] & spr_sr[`OR1K_SPR_SR_TEE] & 
				   !op_mtspr & !doing_rfe &
				   // Stops back-to-back branch addresses to 
				   // fetch  stage.
				   !ctrl_branch_occur_i &
				   // Stops issues with PC when branching
				   !execute_delay_slot;

	 /* SPR bus reads */
	 /* always single cycle access */
	 assign spr_access_ack[10] = 1;
	 assign spr_internal_read_dat[10] =  (spr_addr==`OR1K_SPR_TTCR_ADDR) ?
					     spr_ttcr :
					     (spr_addr==`OR1K_SPR_TTMR_ADDR) ?
					     spr_ttmr : 0;
	 
      end // if (FEATURE_TIMER!="NONE")
      else begin
	 
	 assign except_ticktimer = 0;
	 
	 always @(posedge clk) begin
	    spr_ttmr <= 0;
	    spr_ttcr <= 0;
	 end

	 assign spr_access_ack[10] = 0;
	 
      end // else: !if(FEATURE_TIMER!="NONE")
   endgenerate

   /* SPR access control - allow accesses from either the instructions or from
    the debug interface */
   assign spr_read_access = (op_mfspr | (du_access & !du_we_i));
   assign spr_write_access = (op_mtspr | (du_access & du_we_i));

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
	 reg [3:0] 			pstep_r;
	 reg [1:0] 			branch_step;
	 reg 				stepped_into_exception;
	 reg 				stepped_into_rfe;
	 
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
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     du_read_dat <= 0;
	   else if (spr_access_ack[spr_group]) begin
	      du_read_dat <= spr_internal_read_dat[spr_group];
	   end

	 assign du_dat_o = du_read_dat;
	 /* TODO: check into only letting stall go high when we've gracefully
	  completed the instruction currently in the ctrl stage.
	  Why? Potentially an instruction like l.mfspr from an external unit
	  hasn't completed fully, gets interrupted, and it's assumed it's
	  completed, but actually hasn't. */
	 assign cpu_stall = du_stall_i | du_restart_from_stall;	 	 
	 
	 /* goes out to the debug interface and comes back 1 cycle later
	  via du_stall_i */
	 assign du_stall_o = /* execute stage */
			     (stepping & padv_ctrl);
	 
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
	     du_spr_npc <= 0;
	   else if (du_npc_write)
	     du_spr_npc <= du_dat_i;

	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     stepped_into_exception <= 0;
	   else if (du_restart_from_stall)
	     stepped_into_exception <= 0;
	   else if (stepping & padv_ctrl)
	     stepped_into_exception <= exception;
	 
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     stepped_into_rfe <= 0;
	   else if (du_restart_from_stall)
	     stepped_into_rfe <= 0;
	   else if (stepping & padv_ctrl)
	     stepped_into_rfe <= op_rfe;
	 
	 assign du_restart_pc_o = du_npc_written ? du_spr_npc :
				  stepped_into_rfe ? spr_epcr :
				  stepped_into_delay_slot ?
				  last_branch_target_pc : 
				  stepped_into_exception ? exception_pc_addr : 
				  pc_ctrl_i + 4;

	 assign du_restart_o = du_restart_from_stall;
	 
	 /* Indicate when we're stepping */
	 assign stepping = spr_dmr1[`OR1K_SPR_DMR1_ST] &
			   spr_dsr[`OR1K_SPR_DSR_TE];

	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     pstep_r <= 0;
	   else if (du_restart_from_stall & stepping)
	     pstep_r <= 4'h1;
	   else if ((pstep[0] & fetch_valid_i) |
		    /* decode is always single cycle */
		    (pstep[1] & padv_decode_o) | 
		    (pstep[2] & execute_valid_i))
	     pstep_r <= {pstep_r[2:0],1'b0};
	 
	 assign pstep = pstep_r;

	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     branch_step <= 0;
	   else if (stepping & pstep[2])
	     branch_step <= {branch_step[0], ctrl_branch_occur_i};
	   else if (!stepping & padv_ctrl)
	     branch_step <= {branch_step[0], execute_delay_slot};

	 assign stepped_into_delay_slot = branch_step[1];
	 
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
	   assign spr_access_ack[6] = 0;

	   always @(posedge clk)
	     begin
		spr_dmr1 = 0;
		spr_dmr2 = 0;
		spr_dsr = 0;
		spr_drr = 0;
		du_npc_written = 0;
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
	 assign spr_access_ack[1] = 0;
	 assign spr_internal_read_dat[1] = 0;
      end
   endgenerate

   generate
      if (FEATURE_IMMU!="NONE") begin : immu_ctrl
	 assign spr_access_ack[2] = spr_bus_ack_immu_i;
	 assign spr_internal_read_dat[2] = spr_bus_dat_immu_i;
      end
      else begin
	 assign spr_access_ack[2] = 0;
	 assign spr_internal_read_dat[2] = 0;
      end
   endgenerate

   generate
      if (FEATURE_DATACACHE!="NONE") begin : datacache_ctrl
	 assign spr_access_ack[3] = spr_bus_ack_dc_i;
	 assign spr_internal_read_dat[3] = spr_bus_dat_dc_i;
      end
      else begin
	 assign spr_access_ack[3] = 0;
	 assign spr_internal_read_dat[3] = 0;	 
      end
   endgenerate

   generate
      if (FEATURE_INSTRUCTIONCACHE!="NONE") begin : instructioncache_ctrl
	 assign spr_access_ack[4] = spr_bus_ack_ic_i;
	 assign spr_internal_read_dat[4] = spr_bus_dat_ic_i;
      end
      else begin
	 assign spr_access_ack[4] = 0;
	 assign spr_internal_read_dat[4] = 0;
      end
   endgenerate

   generate
      if (FEATURE_MAC!="NONE") begin : mac_ctrl
	 assign spr_access_ack[5] = spr_bus_ack_mac_i;
	 assign spr_internal_read_dat[5] = spr_bus_dat_mac_i;
      end
      else begin
	 assign spr_access_ack[5] = 0;
	 assign spr_internal_read_dat[5] = 0;
      end
   endgenerate
   
   generate
      if (FEATURE_PERFCOUNTERS!="NONE") begin : perfcounters_ctrl
	 assign spr_access_ack[7] = spr_bus_ack_pcu_i;
	 assign spr_internal_read_dat[7] = spr_bus_dat_pcu_i;
      end
      else begin
	 assign spr_access_ack[7] = 0;
	 assign spr_internal_read_dat[7] = 0;
      end
   endgenerate

   generate
      if (FEATURE_PMU!="NONE") begin : pmu_ctrl
	 assign spr_access_ack[8] = spr_bus_ack_pmu_i;
	 assign spr_internal_read_dat[8] = spr_bus_dat_pcu_i;
      end
      else begin
	 assign spr_access_ack[8] = 0;
	 assign spr_internal_read_dat[8] = 0;
      end
   endgenerate

   generate
      if (FEATURE_FPU!="NONE") begin : fpu_ctrl
	 assign spr_access_ack[11] = spr_bus_ack_fpu_i;
	 assign spr_internal_read_dat[11] = spr_bus_dat_fpu_i;
      end
      else begin
	 assign spr_access_ack[11] = 0;
	 assign spr_internal_read_dat[11] = 0;
      end
   endgenerate

   
   
   
endmodule // mor1kx_ctrl_cappuccino

