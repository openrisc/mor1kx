/*
 * mor1kx espresso fetch unit
 * 
 * Fetch insn, advance PC (or take new branch address) on padv_i.
 * 
 * What we might want to do is have a 1-insn buffer here, so when the current
 * insn is fetched, but the main pipeline doesn't want it yet
 * 
 * indicate ibus errors
 * 
 * */

`include "mor1kx-defines.v"

module mor1kx_fetch_espresso
  (/*AUTOARG*/
   // Outputs
   ibus_adr_o, ibus_req_o, decode_insn_o, next_fetch_done_o,
   fetch_rfa_adr_o, fetch_rfb_adr_o, pc_fetch_o,
   decode_except_ibus_err_o, fetch_advancing_o,
   // Inputs
   clk, rst, ibus_err_i, ibus_ack_i, ibus_dat_i, padv_i,
   branch_occur_i, branch_dest_i, du_restart_i, du_restart_pc_i,
   fetch_take_exception_branch_i
   );

   parameter OPTION_OPERAND_WIDTH = 32;
   parameter OPTION_RF_ADDR_WIDTH = 5;   
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
   output reg [`OR1K_INSN_WIDTH-1:0] 	 decode_insn_o;
   // Indication to pipeline control that the fetch is valid
   output  				 next_fetch_done_o;

   output [OPTION_RF_ADDR_WIDTH-1:0] 	 fetch_rfa_adr_o;
   output [OPTION_RF_ADDR_WIDTH-1:0] 	 fetch_rfb_adr_o;

   // Signal back to the control
   output [OPTION_OPERAND_WIDTH-1:0] 	 pc_fetch_o;
   
   
   // branch/jump indication
   input 				  branch_occur_i;
   input [OPTION_OPERAND_WIDTH-1:0] 	  branch_dest_i;

   // restart signals from debug unit
   input 				  du_restart_i;
   input [OPTION_OPERAND_WIDTH-1:0] 	  du_restart_pc_i;

   input 				  fetch_take_exception_branch_i;
   
   // instruction ibus error indication out
   output reg 				  decode_except_ibus_err_o;

   output 				  fetch_advancing_o;

   // registers
   reg [OPTION_OPERAND_WIDTH-1:0] 	  pc_fetch;
   reg 					  fetch_req;
   reg 					  pc_fetched;
   reg [OPTION_OPERAND_WIDTH-1:0] 	  insn_buffer;
   reg 					  branch_occur_r;
   reg 					  bus_access_done_re_r;
   
   
   wire [OPTION_OPERAND_WIDTH-1:0] 	  pc_fetch_next;
   wire 				  bus_access_done;
   
   assign bus_access_done =  ibus_ack_i | ibus_err_i;

   assign pc_fetch_next = pc_fetch + 4;

   assign ibus_adr_o = pc_fetch;
   assign ibus_req_o = fetch_req;

   assign fetch_advancing_o = (padv_i | fetch_take_exception_branch_i) & 
			      next_fetch_done_o;
   
   // Early RF address fetch
   assign fetch_rfa_adr_o = insn_buffer[`OR1K_RA_SELECT];
   assign fetch_rfb_adr_o = insn_buffer[`OR1K_RB_SELECT];
   
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       pc_fetch <= OPTION_RESET_PC;
     else if ((padv_i & bus_access_done) | fetch_take_exception_branch_i | 
	      bus_access_done)
       // next PC - are we going somewhere else or advancing?
       pc_fetch <= du_restart_i ? du_restart_pc_i :
		   branch_occur_i ? branch_dest_i :
		   pc_fetch_next;

   // Actually goes to pipeline control
   assign pc_fetch_o = pc_fetch;
   
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       fetch_req <= 1;
     else if (padv_i | fetch_take_exception_branch_i)
       fetch_req <= 1;
     else if (bus_access_done & fetch_take_exception_branch_i)
       fetch_req <= 0;

   reg 					  bus_access_done_r;
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       begin
	  bus_access_done_r <= 0;
	  branch_occur_r <= 0;	  
       end
     else
       begin
	  bus_access_done_r <= bus_access_done;
	  branch_occur_r <= branch_occur_i;
       end
   
   assign next_fetch_done_o = bus_access_done_r;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       decode_insn_o <= {`OR1K_OPCODE_NOP,26'd0};
     else if (fetch_take_exception_branch_i)
       // Put a NOP in the pipeline when doing a branch - remove any state
       // which may be causing the exception
       decode_insn_o <= {`OR1K_OPCODE_NOP,26'd0};
     else if ((padv_i & (bus_access_done_r | bus_access_done) & 
	       !branch_occur_r) |
	      // This case is when we stalled to get the delay-slot instruction
	      // and we don't get enough padv to push it through the buffer
	      (branch_occur_i & !bus_access_done & bus_access_done_r & 
	       padv_i & bus_access_done_re_r) )
       decode_insn_o <= insn_buffer;
   
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       decode_except_ibus_err_o <= 0;
     else if ((padv_i | fetch_take_exception_branch_i) & branch_occur_i)
       decode_except_ibus_err_o <= 0;
     else if (fetch_req)
       decode_except_ibus_err_o <= ibus_err_i;
   
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       insn_buffer <= {`OR1K_OPCODE_NOP,26'd0};
     else if (ibus_ack_i)
       insn_buffer <= ibus_dat_i;

   // Register rising edge on bus_access_done
    always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       bus_access_done_re_r <= 0;
     else
       bus_access_done_re_r <= bus_access_done & !bus_access_done_r;
   
endmodule // mor1kx_fetch_espresso

