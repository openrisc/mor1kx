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
				 `OR1K_RESET_VECTOR,8'd0}
    )
   (
    input 				  clk,
    input 				  rst,

    // interface to ibus
    input 				  ibus_err_i,
    input 				  ibus_ack_i,
    input [`OR1K_INSN_WIDTH-1:0] 	  ibus_dat_i,

    // pipeline control input
    input 				  padv_i,

    // interface to decode unit
    output reg [OPTION_OPERAND_WIDTH-1:0] pc_decode_o,
    output reg [`OR1K_INSN_WIDTH-1:0] 	  decode_insn_o,
    output reg 				  fetch_valid_o,

    // interface to icache/ibus
    output [OPTION_OPERAND_WIDTH-1:0] 	  pc_addr_o,
    output [OPTION_OPERAND_WIDTH-1:0] 	  pc_fetch_o,

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

   assign bus_access_done =  ibus_ack_i | ibus_err_i;
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

   assign pc_addr_o = pc_addr;
   assign pc_fetch_o = pc_fetch;

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
	padv_addr <= !stall_adv & !ibus_err_i & !du_restart_i;

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
     else if (ibus_ack_i & padv_i | stall_adv)
       decode_insn_o <= ibus_dat_i;
     else if (ibus_err_i)
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
     else if (ibus_err_i)
       decode_except_ibus_err_o <= 1;
     else if (decode_except_ibus_err_o & branch_occur_i)
       decode_except_ibus_err_o <= 0;

endmodule // mor1kx_fetch_cappuccino

