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
    input [OPTION_OPERAND_WIDTH-1:0] 	  branch_dest_i,
    input [OPTION_OPERAND_WIDTH-1:0] 	  du_restart_pc_i,
    input 				  du_restart_i,

    // pipeline flush input from control unit
    input 				  pipeline_flush_i,

    // instruction ibus error indication out
    output reg 				  decode_except_ibus_err_o,

    output reg 				  fetch_branch_taken_o
   );

   // registers
   reg [OPTION_OPERAND_WIDTH-1:0] 	  pc_fetch;
   reg [OPTION_OPERAND_WIDTH-1:0] 	  pc_addr;
   reg 					  branch_fetch_valid;
   reg 					  branch_occur_r;
   reg 					  padv_addr;

   wire 				  bus_access_done;
   wire 				  branch_occur_edge;
   wire					  delay_slot;
   wire					  kill_fetch;
   wire					  stall_fetch_valid;
   wire					  stall_adv;

   wire 				  imem_err;
   wire 				  imem_ack;
   wire [`OR1K_INSN_WIDTH-1:0] 		  imem_dat;

   assign bus_access_done =  imem_ack | imem_err;
   assign branch_occur_edge = branch_occur_i & !branch_occur_r;

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


   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       branch_occur_r <= 1'b0;
     else
       branch_occur_r <= branch_occur_i;

   // calculate address stage pc
   always @(*)
      if (rst)
	pc_addr = OPTION_RESET_PC;
      else if (du_restart_i)
	pc_addr = du_restart_pc_i;
      else if (branch_occur_i & !fetch_branch_taken_o)
	pc_addr = branch_dest_i;
      else if (padv_addr)
	pc_addr = pc_fetch + 4;
      else
	pc_addr = pc_fetch;

   // address stage advance signal generation
   always @(posedge clk `OR_ASYNC_RST)
      if (rst)
	padv_addr <= 1'b1;
      else
	padv_addr <= !stall_adv & !imem_err & !du_restart_i;

   // Register fetch pc from address stage
   always @(posedge clk `OR_ASYNC_RST)
      if (rst)
	pc_fetch <= OPTION_RESET_PC;
      else if (bus_access_done & padv_i | stall_adv | kill_fetch | du_restart_i)
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
      else if (kill_fetch | pipeline_flush_i | padv_i & !padv_addr)
	fetch_valid_o <= 1'b0;
      else if (bus_access_done | stall_fetch_valid)
	fetch_valid_o <= 1'b1;
      else
	fetch_valid_o <= 1'b0;

   // Register instruction coming in
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       decode_insn_o <= 0;
     else if (imem_ack & padv_i | stall_adv)
       decode_insn_o <= imem_dat;
     else if (imem_err)
       decode_insn_o <= {`OR1K_OPCODE_NOP,26'd0};

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
     else if (decode_except_ibus_err_o & branch_occur_i)
       decode_except_ibus_err_o <= 0;

   /* mor1kx_icache AUTO_TEMPLATE (
    // Outputs
    .cpu_err_o			(imem_err),
    .cpu_ack_o			(imem_ack),
    .cpu_dat_o			(imem_dat),
    .spr_bus_dat_o		(spr_bus_dat_ic_o),
    .spr_bus_ack_o		(spr_bus_ack_ic_o),
    // Inputs
    .ic_enable			(ic_enable),
    .pc_addr_i			(pc_addr),
    .pc_fetch_i			(pc_fetch),
    .padv_fetch_i		(padv_i),
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
      .cpu_err_o			(imem_err),		 // Templated
      .cpu_ack_o			(imem_ack),		 // Templated
      .cpu_dat_o			(imem_dat),		 // Templated
      .ibus_adr_o			(ibus_adr_o[31:0]),
      .ibus_req_o			(ibus_req_o),
      .spr_bus_dat_o			(spr_bus_dat_ic_o),	 // Templated
      .spr_bus_ack_o			(spr_bus_ack_ic_o),	 // Templated
      // Inputs
      .clk				(clk),
      .rst				(rst),
      .ic_enable			(ic_enable),		 // Templated
      .pc_addr_i			(pc_addr),		 // Templated
      .pc_fetch_i			(pc_fetch),		 // Templated
      .padv_fetch_i			(padv_i),		 // Templated
      .ibus_err_i			(ibus_err_i),
      .ibus_ack_i			(ibus_ack_i),
      .ibus_dat_i			(ibus_dat_i[31:0]),
      .spr_bus_addr_i			(spr_bus_addr_i[15:0]),
      .spr_bus_we_i			(spr_bus_we_i),
      .spr_bus_stb_i			(spr_bus_stb_i),
      .spr_bus_dat_i			(spr_bus_dat_i[OPTION_OPERAND_WIDTH-1:0]));
endmodule // mor1kx_fetch_cappuccino
