/* ****************************************************************************
  This Source Code Form is subject to the terms of the 
  Open Hardware Description License, v. 1.0. If a copy 
  of the OHDL was not distributed with this file, You 
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: mor1kx pronto espresso fetch unit
  
  Fetch insn, advance PC (or take new branch address) on padv_i.
  
  What we might want to do is have a 1-insn buffer here, so when the current
  insn is fetched, but the main pipeline doesn't want it yet
  
  indicate ibus errors
 
  Copyright (C) 2012 Authors
 
  Author(s): Julius Baxter <juliusbaxter@gmail.com>
 
***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_fetch_prontoespresso
  (/*AUTOARG*/
   // Outputs
   ibus_adr_o, ibus_req_o, decode_insn_o, fetched_pc_o, fetch_ready_o,
   fetch_rfa_adr_o, fetch_rfb_adr_o, fetch_rf_re_o, pc_fetch_o,
   pc_fetch_next_o, decode_except_ibus_err_o, fetch_sleep_o,
   // Inputs
   clk, rst, ibus_err_i, ibus_ack_i, ibus_dat_i, padv_i,
   branch_occur_i, branch_dest_i, du_restart_i, du_restart_pc_i,
   fetch_take_exception_branch_i, execute_waiting_i, du_stall_i,
   stepping_i, flag_i, flag_clear_i, flag_set_i
   );

   parameter OPTION_OPERAND_WIDTH = 32;
   parameter OPTION_RF_ADDR_WIDTH = 5;   
   parameter OPTION_RESET_PC = {{(OPTION_OPERAND_WIDTH-13){1'b0}},
				`OR1K_RESET_VECTOR,8'd0};

   input clk, rst;
   
   // interface to ibus
   output [OPTION_OPERAND_WIDTH-1:0] ibus_adr_o;
   output 			     ibus_req_o;
   input 			     ibus_err_i;
   input 			     ibus_ack_i;
   input [`OR1K_INSN_WIDTH-1:0]      ibus_dat_i;

   // pipeline control input
   input 			      padv_i;
   
   // interface to decode unit
   output reg [`OR1K_INSN_WIDTH-1:0]  decode_insn_o;
   
   // PC of the current instruction, SPR_PPC basically
   output reg [OPTION_OPERAND_WIDTH-1:0] fetched_pc_o;
   
   // Indication to pipeline control that the fetch stage is ready
   output 				 fetch_ready_o;

   // Signals going to register file to do the read access as we
   // register the instruction out to the decode stage
   output [OPTION_RF_ADDR_WIDTH-1:0] 	 fetch_rfa_adr_o;
   output [OPTION_RF_ADDR_WIDTH-1:0] 	 fetch_rfb_adr_o;
   output 				 fetch_rf_re_o;

   // Signal back to the control
   output [OPTION_OPERAND_WIDTH-1:0] 	 pc_fetch_o;
   output [OPTION_OPERAND_WIDTH-1:0] 	 pc_fetch_next_o;
   
   
   // branch/jump indication
   input 				  branch_occur_i;
   input [OPTION_OPERAND_WIDTH-1:0] 	  branch_dest_i;

   // restart signals from debug unit
   input 				  du_restart_i;
   input [OPTION_OPERAND_WIDTH-1:0] 	  du_restart_pc_i;

   input 				  fetch_take_exception_branch_i;

   input 				  execute_waiting_i;

   // CPU is stalled
   input 				  du_stall_i;
   
   // We're single stepping - this should cause us to fetch only a single insn
   input 				  stepping_i;

   // Flag status information
   input 				  flag_i, flag_clear_i, flag_set_i;
      
   // instruction ibus error indication out
   output reg 				  decode_except_ibus_err_o;

   // fetch sleep mode enabled (due to jump-to-self instruction
   output 				  fetch_sleep_o;

   // Registers
   reg [OPTION_OPERAND_WIDTH-1:0] 	  pc;
   reg 					  fetch_req;
   reg 					  next_insn_will_branch;
   reg 					  have_early_pc_next;
   reg 					  jump_insn_in_decode;
   reg 					  took_early_calc_pc;
   reg 					  padv_r;
   reg 					  took_branch;
   reg 					  execute_waiting_r;
   reg 					  sleep;
   
   
   // Wires
   wire [OPTION_OPERAND_WIDTH-1:0] 	  pc_fetch_next;
   wire [OPTION_OPERAND_WIDTH-1:0] 	  pc_plus_four;
   wire [OPTION_OPERAND_WIDTH-1:0] 	  early_pc_next;
   wire 				  padv_deasserted;
   wire [`OR1K_OPCODE_WIDTH-1:0] 	  next_insn_opcode;
   wire 				  will_go_to_sleep;
   
   assign pc_plus_four		= pc + 4;

   assign pc_fetch_next         = have_early_pc_next ? 
				  early_pc_next : pc_plus_four;
   
   assign ibus_adr_o		= pc;
   assign ibus_req_o		= fetch_req & !fetch_take_exception_branch_i
				  // This is needed in the case that:
				  // 1. a burst just finished and ack in went low because of this
				  // 2. the instruction we just ACKed is a multicycle insn so the 
				  //    execute_waiting_i goes high, but the bus interface will have
				  //    already put out the request onto the bus. It causes a bug
				  //    if we deassert the req from here 1 cycle later, so put this
				  //    signal into the assign logic so that the first cycle of it
				  //    causes req to go low, after which fetch_req is deasserted
				  //    and should handle it
				  & !(execute_waiting_i & fetch_req);

   assign fetch_ready_o		= ibus_ack_i | jump_insn_in_decode;

   assign pc_fetch_o            = pc;
   assign pc_fetch_next_o       = pc_fetch_next;
   
   // Register file control
   assign fetch_rfa_adr_o	= ibus_dat_i[`OR1K_RA_SELECT];
   assign fetch_rfb_adr_o	= ibus_dat_i[`OR1K_RB_SELECT];
   assign fetch_rf_re_o		= ibus_ack_i & padv_i;

   // Pick out opcode of next instruction to go to decode stage
   assign next_insn_opcode      = ibus_dat_i[`OR1K_OPCODE_SELECT];

   // Can calculate next PC based on instruction coming in
   assign early_pc_next = {OPTION_OPERAND_WIDTH{have_early_pc_next}} &
			  ({{4{ibus_dat_i[25]}},
			    ibus_dat_i[`OR1K_JUMPBRANCH_IMMEDIATE_SELECT],
			    2'b00} + pc);

   assign will_go_to_sleep = have_early_pc_next & 
			     (early_pc_next == pc);

   assign fetch_sleep_o = sleep;
      
   // The pipeline advance signal deasserted for the instruction
   // we just put out, and we're still attempting to fetch. This should
   // result in a deassert cycle on the request signal out to the bus.
   // But, we don't want this to indicate when padv_i was deasserted for
   // a branch, because we will know about that, we just want this to
   // indicate it was deasserted for other reasons.
   assign padv_deasserted = padv_r & !padv_i & fetch_req & !took_branch;
   
   always @*
     if (ibus_ack_i)
       case (next_insn_opcode)
	 `OR1K_OPCODE_J,
	 `OR1K_OPCODE_JAL: begin
	    have_early_pc_next		= 1;
	    next_insn_will_branch	= 1;
	 end
	 `OR1K_OPCODE_JR,
	 `OR1K_OPCODE_JALR: begin
	    have_early_pc_next		= 0;
	    next_insn_will_branch	= 1;
	 end
	 `OR1K_OPCODE_BNF: begin
	    have_early_pc_next		= !(flag_i | flag_set_i) | flag_clear_i;
	    next_insn_will_branch	= !(flag_i | flag_set_i) | flag_clear_i;
	 end
	 `OR1K_OPCODE_BF: begin
	    have_early_pc_next		= !(!flag_i | flag_clear_i) |flag_set_i;
	    next_insn_will_branch	= !(!flag_i | flag_clear_i) |flag_set_i;
	 end
	 `OR1K_OPCODE_SYSTRAPSYNC,
	 `OR1K_OPCODE_RFE: begin
	    have_early_pc_next		= 0;
	    next_insn_will_branch	= 1;
	 end
	 default: begin
	   have_early_pc_next		= 0;
	   next_insn_will_branch	= 0;
	 end
       endcase // case (next_insn_opcode)
     else 
       begin
	  have_early_pc_next		= 0;
	  next_insn_will_branch		= 0;
       end
   
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       begin
	  pc		<= OPTION_RESET_PC;
	  fetched_pc_o	<= OPTION_RESET_PC;
       end
     else if (ibus_ack_i & padv_i)
       begin
	  pc		<= pc_fetch_next_o;
	  fetched_pc_o	<= pc;
       end
     else if (branch_occur_i & !took_early_calc_pc)
       begin
	  pc		<= branch_dest_i;
       end
     else if (fetch_take_exception_branch_i)
       begin
	  pc		<= branch_dest_i;
       end
       
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       decode_insn_o <= {`OR1K_OPCODE_NOP,26'd0};
     else if (sleep)
       decode_insn_o <= {`OR1K_OPCODE_NOP,26'd0};
     else if (ibus_ack_i & padv_i & !padv_deasserted)
       decode_insn_o <= ibus_dat_i;
     else if (branch_occur_i & padv_i)
       /* We've just taken a branch, put a nop
	on the instruction to the rest of the pipeline */
       decode_insn_o <= {`OR1K_OPCODE_NOP,26'd0};
     else if (fetch_take_exception_branch_i)
       /* exception was just taken, get rid of whatever we're outputting */
       decode_insn_o <= {`OR1K_OPCODE_NOP,26'd0};

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       fetch_req <= 1'b1;
     else if (ibus_err_i)
       fetch_req <= 1'b0;
     else if (sleep)
       fetch_req <= 1'b0;
     else if (next_insn_will_branch)
       fetch_req <= 1'b0;
     else if (execute_waiting_i)
       /* 
	Put the execute wait signal through this register to break any long 
	chains of logic from the execute stage (LSU, ALU) which could result 
	from using it to just gate the req signal out.
	TODO - actually check the impact of gating fetch_req_o with 
	       execute_waiting_i 
	*/
       fetch_req <= 1'b0;
     else if (padv_deasserted)
       fetch_req <= 1'b0;
     else
       fetch_req <= 1'b1;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       jump_insn_in_decode <= 0;
     else if (sleep)
       jump_insn_in_decode <= 0;
     else if (!jump_insn_in_decode & next_insn_will_branch & ibus_ack_i)
       jump_insn_in_decode <= 1;
     else
       jump_insn_in_decode <= 0;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       took_early_calc_pc <= 0;
     else if (sleep)
       took_early_calc_pc <= 0;
     else if (next_insn_will_branch & have_early_pc_next & padv_i)
       took_early_calc_pc <= 1;
     else
       took_early_calc_pc <= 0;
   
   always @(posedge clk)
     padv_r <= padv_i;

   /* Whether it was early branch or not, we've branched, and this
    signal will be asserted the cycle after. */
   always @(posedge clk)
     took_branch <= branch_occur_i & fetch_ready_o;
   
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       decode_except_ibus_err_o <= 0;
     else if ((padv_i | fetch_take_exception_branch_i) & 
	      branch_occur_i | du_stall_i)
       decode_except_ibus_err_o <= 0;
     else if (fetch_req)
       decode_except_ibus_err_o <= ibus_err_i;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       sleep <= 1'b0;
     else if (fetch_take_exception_branch_i)
       sleep <= 1'b0;
     else if (will_go_to_sleep)
       sleep <= 1'b1;
   
   
   
endmodule // mor1kx_fetch_prontoespresso


