/*
 * mor1kx fetch unit
 * 
 * basically an interface to the ibus subsystem that can react to exception
 * and branch signals.
 * 
 * maybe take notice of jump instructions - allow a bit of spec. fetch
 * 
 * indicate ibus errors
 * 
 * */

`include "mor1kx-defines.v"

module mor1kx_fetch_fourstage
  (/*AUTOARG*/
   // Outputs
   ibus_adr_o, ibus_req_o, pc_decode_o, decode_insn_o, fetch_valid_o,
   pc_fetch_next_o, decode_except_ibus_err_o, fetch_branch_taken_o,
   // Inputs
   clk, rst, ibus_err_i, ibus_ack_i, ibus_dat_i, padv_i,
   branch_occur_i, branch_dest_i, du_restart_pc_i, du_restart_i,
   pipeline_flush_i
   );

   parameter OPTION_OPERAND_WIDTH = 32;
   
   parameter OPTION_RESET_PC = {{(OPTION_OPERAND_WIDTH-13){1'b0}},
				`OR1K_RESET_VECTOR,8'd0};

   
   input clk, rst;
   
   // interface to ibus
   output [OPTION_OPERAND_WIDTH-1:0] ibus_adr_o;
   output 			      ibus_req_o;
   input 			      ibus_err_i;
   input 			      ibus_ack_i;
   input [`OR1K_INSN_WIDTH-1:0]       ibus_dat_i;

   // pipeline control input
   input 			      padv_i;
   
   // interface to decode unit
   output reg [OPTION_OPERAND_WIDTH-1:0] pc_decode_o;
   output reg [`OR1K_INSN_WIDTH-1:0] 	  decode_insn_o;
   output reg 				  fetch_valid_o;
   output [OPTION_OPERAND_WIDTH-1:0]	  pc_fetch_next_o;
   
   // branch/jump indication
   input 				  branch_occur_i;
   input [OPTION_OPERAND_WIDTH-1:0] 	  branch_dest_i;
   input [OPTION_OPERAND_WIDTH-1:0] 	  du_restart_pc_i;
   input 				  du_restart_i;

   // pipeline flush input from control unit
   input 				  pipeline_flush_i;
   
   
   // instruction ibus error indication out
   output reg 				  decode_except_ibus_err_o;

   output reg 				  fetch_branch_taken_o;

   // registers
   reg [OPTION_OPERAND_WIDTH-1:0] 	  pc_fetch;   
   reg 					  pc_fetched;
   reg 					  pc_fetched_r;
   wire 				  zero_cycle_stall;
   reg 					  zero_cycle_stall_r;
   reg 					  fetch_in_progress;
   reg 					  branch_fetch;
   reg 					  padv_r;
   reg 					  will_branch;
   reg 					  branch_occur_r;
   wire 				  branch_occur_re;
   wire 				  discard_current_fetch;
   reg 					  discard_current_fetch_r;
   reg 					  current_fetch_discarded;
   wire 				  pc_fetch_advance;
   wire 				  pc_fetch_take_branch_addr;
   reg 					  du_restart_r;
   reg 					  pc_fetch_advance_r;
   
   wire [OPTION_OPERAND_WIDTH-1:0] 	  pc_fetch_next;
   wire 				  bus_access_done;
   
   assign bus_access_done =  ibus_ack_i | ibus_err_i;

   assign pc_fetch_next = pc_fetch + 4;
   assign pc_fetch_next_o = pc_fetch_next;

   assign pc_fetch_advance =  // not fetching and not just unstalled by DU
			      (!ibus_req_o & !fetch_valid_o & !du_restart_r) |
			      // end of normal fetch cycle.
			      // the not fetch_branch_taken_o stops the case of
			      // a new branch PC being incremented when an extra
			      // ack from the previous fetches got through to us
			      // after we've taken the new addr, thus
			      // incrementing it before it's fetched
			      (ibus_ack_i & padv_i & !fetch_branch_taken_o)    |
			      // end of stalled fetch cycle
			      (pc_fetched & padv_i)    |
			      // end of bus excpt
			      (decode_except_ibus_err_o & branch_occur_i) |
			      // Just had an ACK, branch is incoming
			      (branch_occur_i & fetch_valid_o & !branch_fetch);

   assign pc_fetch_take_branch_addr = (branch_occur_i & 
				       ((!branch_fetch)|discard_current_fetch));
   
   
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       pc_fetch <= OPTION_RESET_PC;
     else if (pc_fetch_advance)
       // next PC - are we going somewhere else or advancing?
       pc_fetch <= du_restart_i ? du_restart_pc_i :
		   pc_fetch_take_branch_addr ? branch_dest_i :
		   !(pc_fetched & !padv_i) ? pc_fetch_next :
		   pc_fetch;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       branch_occur_r <= 0;
     else
       branch_occur_r <= branch_occur_i;

   // Detect rising edge on incoming branch indicator signal
   assign branch_occur_re = branch_occur_i & !branch_occur_r;

   // Detect an acked discarded fetch in the case where
   // the bus access is acked at the same time as the current
   // fetch is deemed to be discarded.
   // This is then used to clear the discard_current_fetch in the
   // next cycle.
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       current_fetch_discarded <= 0;
     else if (discard_current_fetch & bus_access_done)
       current_fetch_discarded <= 1;
     else
       current_fetch_discarded <= 0;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       discard_current_fetch_r <= 0;
     else if ((discard_current_fetch_r & bus_access_done) |
	      current_fetch_discarded)
       discard_current_fetch_r  <= 0;
     else if (branch_occur_re & branch_fetch)
       discard_current_fetch_r <= 1;

   assign discard_current_fetch = (branch_occur_re & branch_fetch) |
				  discard_current_fetch_r;

   // Asserted when branch indication comes in, but we're in the middle of
   // waiting for another fetch. (In the case of branch indication coming in
   // and we're streaming in instructions, fetch PC changes instantly.)
   // This is then used to put out new fetch PC after next ACK from fetch
   // interface.
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       will_branch <= 0;
     else if (will_branch & ibus_ack_i)
       will_branch <= 0;
     else if (!will_branch)
       will_branch <= branch_occur_i & !ibus_ack_i;


   // Indicates if this fetch is in response to a branch request
    always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       branch_fetch <= 0;
     else if (bus_access_done | fetch_valid_o)
       branch_fetch <= branch_occur_i;

   /*
   // Pulses when we're acking the first fetch of the branch
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       fetch_branch_taken_o <= 0;
     else 
       fetch_branch_taken_o <= ibus_ack_i & branch_fetch;
*/
    // Pulses when branch address goes out onto bus
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       fetch_branch_taken_o <= 0;
     else if (fetch_branch_taken_o)
       fetch_branch_taken_o <= 0;
     else if (pc_fetch_advance)
       fetch_branch_taken_o <= pc_fetch_take_branch_addr;
   
   // Signal to indicate if we've seen a new advance request since the last.
   // Detects when later parts of pipeline have stalled while we've fetched.
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       pc_fetched <= 0;
     else if (padv_i | du_restart_i)
       pc_fetched <= 0;
     else if ((bus_access_done) & !padv_i)
       pc_fetched <= 1'b1;

   always @(posedge clk)
     pc_fetched_r <= pc_fetched;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       fetch_in_progress <= 0;
     else if (ibus_ack_i & !padv_i)
       fetch_in_progress <= 0;
     else if (padv_i)
       fetch_in_progress <= 1;
   
   assign ibus_adr_o = pc_fetch ;
   assign ibus_req_o = (padv_i | 
		       (fetch_in_progress  & !(!padv_i & fetch_valid_o))) &
		       !decode_except_ibus_err_o &
		       // stops address changing 1 cycle after we put req out
		       !(pc_fetch_advance_r & !fetch_in_progress) &
		       // wait one cycle for pc to advance after stalled cycle
		       !(pc_fetched & padv_i) &
		       !(branch_occur_i & fetch_valid_o);

   // Register instruction coming in
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       decode_insn_o <= 0;
     else if (ibus_ack_i)
       decode_insn_o <= ibus_dat_i;
     else if (ibus_err_i)
       decode_insn_o <= {`OR1K_OPCODE_NOP,26'd0};

   // Register PC for later stages
      always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       pc_decode_o <= OPTION_RESET_PC;
     else if (bus_access_done)
       pc_decode_o <= pc_fetch;

   assign zero_cycle_stall = (pc_fetched & !pc_fetched_r & padv_i);

   always @(posedge clk)
     zero_cycle_stall_r <= zero_cycle_stall;

   // Valid signal generation - assert when instruction received and we've not
   // got a branch request. Then keep asserted as long as we're not advancing.
   
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       fetch_valid_o <= 0;
     else if (pipeline_flush_i)
       fetch_valid_o <= 0;
     else if (branch_occur_i & !will_branch & pc_fetch_advance_r)
       fetch_valid_o <= 0;
     else if (bus_access_done & !discard_current_fetch & !fetch_branch_taken_o)
       fetch_valid_o <= 1;
     else
       // Keep valid high if we've fetched an instruction
       // also handle the special case where we are stalling,
       // but get an advance signal at the same time as pc_fetched goes high
       fetch_valid_o <= (!padv_i &
			 (pc_fetched | (fetch_valid_o & !zero_cycle_stall_r))) |
			(zero_cycle_stall & !fetch_valid_o);

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       decode_except_ibus_err_o <= 0;
     else if (du_restart_i)
       decode_except_ibus_err_o <= 0;
     else if (ibus_err_i)
       decode_except_ibus_err_o <= 1;
     else if (decode_except_ibus_err_o & branch_occur_i)
       decode_except_ibus_err_o <= 0;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       padv_r <= 0;
     else
       padv_r <= padv_i;

   // Register du restart signal so we know when we've just done a restart
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       du_restart_r <= 0;
     else
       du_restart_r <= du_restart_i;

   // Register pc_fetch_advance  to break a combinatorial path between it and
   // ibus_req_o
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       pc_fetch_advance_r <= 0;
     else
       pc_fetch_advance_r <= pc_fetch_advance;
   
endmodule // mor1kx_fetch
