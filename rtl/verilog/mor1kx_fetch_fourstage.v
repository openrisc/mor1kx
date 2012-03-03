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
 */

`include "mor1kx-defines.v"

module mor1kx_fetch_fourstage
  (/*AUTOARG*/
   // Outputs
   ibus_adr_o, ibus_req_o, pc_decode_o, decode_insn_o, fetch_valid_o,
   decode_except_ibus_err_o, fetch_branch_taken_o,
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
   output reg			      ibus_req_o;
   input 			      ibus_err_i;
   input 			      ibus_ack_i;
   input [`OR1K_INSN_WIDTH-1:0]       ibus_dat_i;

   // pipeline control input
   input 			      padv_i;

   // interface to decode unit
   output reg [OPTION_OPERAND_WIDTH-1:0] pc_decode_o;
   output reg [`OR1K_INSN_WIDTH-1:0] 	  decode_insn_o;
   output reg 				  fetch_valid_o;

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
   reg [OPTION_OPERAND_WIDTH-1:0] 	  pc_addr;
   reg 					  branch_fetch_valid;
   reg 					  branch_occur_r;

   wire [OPTION_OPERAND_WIDTH-1:0] 	  pc_addr_next;
   wire 				  bus_access_done;
   wire 				  branch_occur_edge;

   // States
   localparam INIT		= 4'd1;
   localparam LOAD_REQ		= 4'd2;
   localparam ADVANCE		= 4'd3;
   localparam STALL		= 4'd4;
   localparam BRANCH_WAITBUS	= 4'd5;
   localparam BRANCH		= 4'd6;
   localparam BRANCH_DONE	= 4'd7;

   reg [3:0] 			  state;
   reg [3:0] 			  pre_stall_state;
   wire 			  advance = (state == ADVANCE);
   wire 			  stall = (state == STALL);
   wire 			  load_req = (state == LOAD_REQ);
   wire 			  branch_waitbus = (state == BRANCH_WAITBUS);

   assign bus_access_done =  ibus_ack_i | ibus_err_i;
   assign ibus_adr_o = pc_addr;
   assign pc_addr_next = pc_addr + 4;
   assign branch_occur_edge = branch_occur_i & !branch_occur_r;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       branch_occur_r <= 1'b0;
     else
       branch_occur_r <= branch_occur_i;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	pc_addr <= OPTION_RESET_PC;
	state <= INIT;
	pre_stall_state <= ADVANCE;
	ibus_req_o <= 1'b0;
     end else begin
	ibus_req_o <= 1'b1;
	fetch_valid_o <= 1'b0;
	fetch_branch_taken_o <= 1'b0;
	case (state)
	  INIT: begin
	     state <= LOAD_REQ;
	  end

	  LOAD_REQ: begin
	     if ((pre_stall_state == ADVANCE) ||
		 (pre_stall_state == BRANCH_DONE))
	       pc_addr <= pc_addr_next;
	     else
	       pc_addr <= branch_dest_i;

	     pc_fetch <= pc_addr;
	     state <= pre_stall_state;
	  end

	  ADVANCE: begin
	     if (branch_occur_i) begin
		if (bus_access_done) begin
		   pc_addr <= branch_dest_i;
		   pc_fetch <= pc_addr;
		   fetch_valid_o <= ~fetch_valid_o;
		   state <= BRANCH;
		end else begin
		   /*
		    * keep track if the ongoing access
		    * should be discarded or if it is valid
		    */
		   branch_fetch_valid <= ~fetch_valid_o;
		   state <= BRANCH_WAITBUS;
		end
	     end else if (bus_access_done) begin
		fetch_valid_o <= 1'b1;
		pc_addr <= pc_addr_next;
		pc_fetch <= pc_addr;
	     end
	  end

	  STALL: begin
	     if (!padv_i)
	       fetch_valid_o <= fetch_valid_o;
	     if (padv_i & !ibus_req_o) begin
		pc_addr <= pc_fetch;
		state <= LOAD_REQ;
	     end else if (ibus_req_o & ibus_ack_i | !ibus_req_o) begin
		ibus_req_o <= 1'b0;
	     end
	  end

	  BRANCH_WAITBUS: begin
	     if (bus_access_done) begin
		fetch_valid_o <= branch_fetch_valid;
		pc_addr <= branch_dest_i;
		pc_fetch <= pc_addr;
		state <= BRANCH;
	     end
	  end

	  BRANCH: begin
	     /*
	      * check for a new incoming branch while branching,
	      * for example an exception in delay slot
	      */
	     if (branch_occur_edge) begin
		if (bus_access_done) begin
		   pc_addr <= branch_dest_i;
		   state <= BRANCH;
		end else begin
		   state <= BRANCH_WAITBUS;
		end
	     end else if (bus_access_done) begin
		pc_addr <= pc_addr_next;
		pc_fetch <= pc_addr;
		fetch_branch_taken_o <= 1'b1;
		state <= BRANCH_DONE;
	     end
	  end

	  BRANCH_DONE: begin
	     if (bus_access_done) begin
		pc_addr <= pc_addr_next;
		pc_fetch <= pc_addr;
		fetch_valid_o <= 1'b1;
		state <= ADVANCE;
	     end
	  end
	endcase

	/*
	 * deassertion of padv_i overrides all other
	 * state transitions. The current state is saved
	 * and pc_addr and pc_fetch keep their values
	 */
	if (!padv_i & !stall & !load_req) begin
	   if (ibus_req_o & ibus_ack_i)
	     ibus_req_o <= 1'b0;
	   pc_addr <= pc_addr;
	   pc_fetch <= pc_fetch;
	   fetch_valid_o <= fetch_valid_o;
	   fetch_branch_taken_o <= 1'b0;
	   pre_stall_state <= state;
	   state <= STALL;
	end

	/*
	 * a debug unit restart also overrides all other states
	 * and resets the FSM
	 */
	if (du_restart_i) begin
	   pc_addr <= du_restart_pc_i;
	   ibus_req_o <= 1'b1;
	   fetch_valid_o <= 1'b0;
	   fetch_branch_taken_o <= 1'b0;
	   pre_stall_state <= ADVANCE;
	   state <= LOAD_REQ;
	end
     end

   // Register instruction coming in
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       decode_insn_o <= 0;
     else if (ibus_ack_i & padv_i & !stall)
       decode_insn_o <= ibus_dat_i;
     else if (ibus_err_i)
       decode_insn_o <= {`OR1K_OPCODE_NOP,26'd0};

   // Register PC for later stages
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       pc_decode_o <= OPTION_RESET_PC;
     else if (bus_access_done & padv_i & !stall)
       pc_decode_o <= pc_fetch;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       decode_except_ibus_err_o <= 0;
     else if (du_restart_i)
       decode_except_ibus_err_o <= 0;
     else if (ibus_err_i)
       decode_except_ibus_err_o <= 1;
     else if (decode_except_ibus_err_o & branch_occur_i)
       decode_except_ibus_err_o <= 0;

endmodule // mor1kx_fetch
