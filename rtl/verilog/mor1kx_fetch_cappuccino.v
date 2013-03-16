/* ****************************************************************************
  This Source Code Form is subject to the terms of the
  Open Hardware Description License, v. 1.0. If a copy
  of the OHDL was not distributed with this file, You
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: mor1kx fetch/address stage unit

  basically an interface to the ibus/icache subsystem that can react to
  exception and branch signals.

  Copyright (C) 2012 Authors

  Author(s): Julius Baxter <juliusbaxter@gmail.com>
             Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_fetch_cappuccino
  #(
    parameter OPTION_OPERAND_WIDTH = 32,
    parameter OPTION_RESET_PC = {{(OPTION_OPERAND_WIDTH-13){1'b0}},
				 `OR1K_RESET_VECTOR,8'd0},
    parameter FEATURE_INSTRUCTIONCACHE = "NONE",
    parameter OPTION_ICACHE_BLOCK_WIDTH = 5,
    parameter OPTION_ICACHE_SET_WIDTH = 9,
    parameter OPTION_ICACHE_WAYS = 2,
    parameter OPTION_ICACHE_LIMIT_WIDTH = 32
    )
   (
    input 				  clk,
    input 				  rst,

    // SPR interface
    input [15:0] 			  spr_bus_addr_i,
    input 				  spr_bus_we_i,
    input 				  spr_bus_stb_i,
    input [OPTION_OPERAND_WIDTH-1:0] 	  spr_bus_dat_i,
    output [OPTION_OPERAND_WIDTH-1:0] 	  spr_bus_dat_ic_o,
    output 				  spr_bus_ack_ic_o,

    input 				  ic_enable,

    // interface to ibus
    input 				  ibus_err_i,
    input 				  ibus_ack_i,
    input [`OR1K_INSN_WIDTH-1:0] 	  ibus_dat_i,
    output 				  ibus_req_o,
    output [OPTION_OPERAND_WIDTH-1:0] 	  ibus_adr_o,

    // pipeline control input
    input 				  padv_i,

    // interface to decode unit
    output reg [OPTION_OPERAND_WIDTH-1:0] pc_decode_o,
    output reg [`OR1K_INSN_WIDTH-1:0] 	  decode_insn_o,
    output reg 				  fetch_valid_o,

    // branch/jump indication
    input 				  branch_occur_i,
    input 				  branch_except_occur_i,
    input [OPTION_OPERAND_WIDTH-1:0] 	  branch_dest_i,
    input [OPTION_OPERAND_WIDTH-1:0] 	  du_restart_pc_i,
    input 				  du_restart_i,

    // pipeline flush input from control unit
    input 				  pipeline_flush_i,

    // rfe instruction is being performed
    input 				  doing_rfe_i,

    // instruction ibus error indication out
    output reg 				  decode_except_ibus_err_o,

    output reg 				  fetch_branch_taken_o
   );

   // registers
   reg [OPTION_OPERAND_WIDTH-1:0] 	  pc_fetch;
   reg [OPTION_OPERAND_WIDTH-1:0] 	  pc_addr;
   reg 					  branch_fetch_valid;
   reg 					  branch_occur_r;
   reg 					  branch_except_occur_r;

   wire 				  bus_access_done;
   wire 				  branch_occur_edge;
   wire 				  branch_except_occur_edge;
   wire					  delay_slot;
   wire					  kill_fetch;
   wire					  stall_fetch_valid;
   wire					  stall_adv;
   wire 				  addr_valid;

   reg 					  fake_ack;

   wire 				  imem_err;
   wire 				  imem_ack;
   wire [`OR1K_INSN_WIDTH-1:0] 		  imem_dat;

   wire 				  ic_err;
   wire 				  ic_ack;
   wire [`OR1K_INSN_WIDTH-1:0] 		  ic_dat;

   wire 				  ic_req;
   wire 				  ic_refill_allowed;
   wire 				  ic_refill;
   wire [OPTION_OPERAND_WIDTH-1:0] 	  ic_addr;
   wire [OPTION_OPERAND_WIDTH-1:0] 	  ic_addr_match;

   wire [OPTION_OPERAND_WIDTH-1:0] 	  ic_ibus_adr;
   wire 				  ic_ibus_req;
   wire 				  ic_access;

   reg 					  ic_enable_r;
   wire 				  ic_enabled;
   assign bus_access_done =  imem_ack | imem_err | fake_ack;
   assign branch_occur_edge = branch_occur_i & !branch_occur_r;
   assign branch_except_occur_edge = branch_except_occur_i &
				     !branch_except_occur_r;

   /*
    * Detect when we are doing a delay slot,
    * in fetch stage we do them on all branches,
    * even on exceptions and rfe (will be discarded later)
    */
   assign delay_slot = branch_occur_i & fetch_valid_o;

   assign kill_fetch = branch_occur_edge & delay_slot;

   /* used to keep fetch_valid_o high during stall */
   assign stall_fetch_valid = !padv_i & fetch_valid_o;

   /* signal to determine if we should advance during a stall */
   assign stall_adv = !padv_i & bus_access_done & !fetch_valid_o;

   assign addr_valid = (bus_access_done & padv_i | stall_adv) |
		       kill_fetch |
		       doing_rfe_i & branch_occur_i;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	branch_occur_r <= 1'b0;
	branch_except_occur_r <= 1'b0;
     end else begin
	branch_occur_r <= branch_occur_i;
	branch_except_occur_r <= branch_except_occur_i;
     end

   // calculate address stage pc
   always @(*)
      if (rst)
	pc_addr = OPTION_RESET_PC;
      else if (du_restart_i)
	pc_addr = du_restart_pc_i;
      else if (branch_occur_i & !fetch_branch_taken_o)
	pc_addr = branch_dest_i;
      else
	pc_addr = pc_fetch + 4;

   // Register fetch pc from address stage
   always @(posedge clk `OR_ASYNC_RST)
      if (rst)
	pc_fetch <= OPTION_RESET_PC;
      else if (addr_valid | du_restart_i)
	pc_fetch <= pc_addr;

   // fetch_branch_taken_o generation
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       fetch_branch_taken_o <= 1'b0;
     else if (fetch_branch_taken_o)
       fetch_branch_taken_o <= 1'b0;
     else if ((branch_occur_i | delay_slot) & bus_access_done & padv_i)
       fetch_branch_taken_o <= 1'b1;
     else
       fetch_branch_taken_o <= 1'b0;

   // fetch_valid_o generation
   always @(posedge clk `OR_ASYNC_RST)
      if (rst)
	fetch_valid_o <= 1'b0;
      else if (kill_fetch | pipeline_flush_i)
	fetch_valid_o <= 1'b0;
      else if (bus_access_done | stall_fetch_valid)
	fetch_valid_o <= 1'b1;
      else
	fetch_valid_o <= 1'b0;

   // Register instruction coming in
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       decode_insn_o <= 0;
     else if (imem_err)
       decode_insn_o <= {`OR1K_OPCODE_NOP,26'd0};
     else if (imem_ack & padv_i | stall_adv)
       decode_insn_o <= imem_dat;

   // Register PC for later stages
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       pc_decode_o <= OPTION_RESET_PC;
     else if (bus_access_done & padv_i | stall_adv)
       pc_decode_o <= pc_fetch;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       decode_except_ibus_err_o <= 0;
     else if (du_restart_i)
       decode_except_ibus_err_o <= 0;
     else if (imem_err)
       decode_except_ibus_err_o <= 1;
     else if (decode_except_ibus_err_o & branch_except_occur_i)
       decode_except_ibus_err_o <= 0;

   // Bus access logic
   localparam [1:0] IDLE = 2'd0;
   localparam [1:0] READ = 2'd1;

   reg [1:0] state;

   reg [OPTION_OPERAND_WIDTH-1:0] ibus_adr;
   reg [`OR1K_INSN_WIDTH-1:0] 	  ibus_dat;
   reg 				  ibus_req;
   reg 				  ibus_ack;
   reg 				  ibus_err;

   wire 			  ibus_access;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       fake_ack <= 0;
     else
       fake_ack <= padv_i & branch_except_occur_edge &
		   !bus_access_done & !ibus_req &
		   !kill_fetch;

   assign ibus_access = !ic_access;
   assign imem_ack = ibus_access ? ibus_ack : ic_ack;
   assign imem_err = ibus_access ? ibus_err : ic_err;
   assign imem_dat = fake_ack ? {`OR1K_OPCODE_NOP,26'd0} :
		     ibus_access ? ibus_dat : ic_dat;
   assign ibus_adr_o = ibus_access ? ibus_adr : ic_ibus_adr;
   assign ibus_req_o = ibus_access ? ibus_req : ic_ibus_req;

   always @(posedge clk) begin
      ibus_ack <= 0;
      ibus_err <= 0;
      case (state)
	IDLE: begin
	   ibus_req <= 0;
	   if (padv_i & ibus_access & !ibus_ack & !ibus_err & !fake_ack) begin
	      if (!branch_except_occur_i | doing_rfe_i) begin
		 ibus_adr <= pc_fetch;
		 ibus_req <= 1;
		 state <= READ;
	      end
	   end
	end

	READ: begin
	   ibus_ack <= ibus_ack_i;
	   ibus_err <= ibus_err_i;
	   ibus_dat <= ibus_dat_i;
	   if (ibus_ack_i | ibus_err_i) begin
	      ibus_req <= 0;
	      state <= IDLE;
	   end
	end
      endcase // case (state)

      if (rst)
	state <= IDLE;
   end

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       ic_enable_r <= 0;
     else if (ic_enable & !ibus_req)
       ic_enable_r <= 1;
     else if (!ic_enable & !ic_refill)
       ic_enable_r <= 0;

   assign ic_enabled = ic_enable & ic_enable_r;
   assign ic_addr = addr_valid ? pc_addr : pc_fetch;
   assign ic_addr_match = pc_fetch;
   assign ic_req = padv_i;
   assign ic_refill_allowed = 1;

generate
if (FEATURE_INSTRUCTIONCACHE!="NONE") begin : icache_gen
   if (OPTION_ICACHE_LIMIT_WIDTH == OPTION_OPERAND_WIDTH) begin
      assign ic_access = ic_enabled;
   end else if (OPTION_ICACHE_LIMIT_WIDTH < OPTION_OPERAND_WIDTH) begin
      assign ic_access = ic_enabled &
			 pc_fetch[OPTION_OPERAND_WIDTH-1:
				  OPTION_ICACHE_LIMIT_WIDTH] == 0;
   end else begin
      initial begin
	 $display("ERROR: OPTION_ICACHE_LIMIT_WIDTH > OPTION_OPERAND_WIDTH");
	 $finish();
      end
   end

   /* mor1kx_icache AUTO_TEMPLATE (
    // Outputs
    .cpu_err_o			(ic_err),
    .cpu_ack_o			(ic_ack),
    .cpu_dat_o			(ic_dat[OPTION_OPERAND_WIDTH-1:0]),
    .ibus_adr_o			(ic_ibus_adr),
    .ibus_req_o			(ic_ibus_req),
    .spr_bus_dat_o		(spr_bus_dat_ic_o),
    .spr_bus_ack_o		(spr_bus_ack_ic_o),
    .refill_o			(ic_refill),
    // Inputs
    .ic_enable			(ic_enabled),
    .addr_i			(ic_addr),
    .addr_match_i		(ic_addr_match),
    .req_i			(ic_req),
    .refill_allowed_i		(ic_refill_allowed),
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
      .refill_o				(ic_refill),		 // Templated
      .cpu_err_o			(ic_err),		 // Templated
      .cpu_ack_o			(ic_ack),		 // Templated
      .cpu_dat_o			(ic_dat[OPTION_OPERAND_WIDTH-1:0]), // Templated
      .ibus_adr_o			(ic_ibus_adr),		 // Templated
      .ibus_req_o			(ic_ibus_req),		 // Templated
      .spr_bus_dat_o			(spr_bus_dat_ic_o),	 // Templated
      .spr_bus_ack_o			(spr_bus_ack_ic_o),	 // Templated
      // Inputs
      .clk				(clk),
      .rst				(rst),
      .ic_enable			(ic_enabled),		 // Templated
      .addr_i				(ic_addr),		 // Templated
      .addr_match_i			(ic_addr_match),	 // Templated
      .req_i				(ic_req),		 // Templated
      .refill_allowed_i			(ic_refill_allowed),	 // Templated
      .ibus_err_i			(ibus_err_i),
      .ibus_ack_i			(ibus_ack_i),
      .ibus_dat_i			(ibus_dat_i[31:0]),
      .spr_bus_addr_i			(spr_bus_addr_i[15:0]),
      .spr_bus_we_i			(spr_bus_we_i),
      .spr_bus_stb_i			(spr_bus_stb_i),
      .spr_bus_dat_i			(spr_bus_dat_i[OPTION_OPERAND_WIDTH-1:0]));
end else begin // block: icache_gen
   assign ic_access = 0;
   assign ic_ack = 0;
   assign ic_err = 0;
   assign ic_ibus_req = 0;
   assign ic_ibus_adr = 0;
end
endgenerate
endmodule // mor1kx_fetch_cappuccino
