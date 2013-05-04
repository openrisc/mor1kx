/******************************************************************************
 This Source Code Form is subject to the terms of the
 Open Hardware Description License, v. 1.0. If a copy
 of the OHDL was not distributed with this file, You
 can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

 Description: Instruction MMU implementation

 Copyright (C) 2013 Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>

 ******************************************************************************/

`include "mor1kx-defines.v"

module mor1kx_immu
  #(
    parameter OPTION_OPERAND_WIDTH = 32,
    parameter OPTION_IMMU_SET_WIDTH = 6,
    parameter OPTION_IMMU_WAYS = 1
    )
   (
    input 			      clk,
    input 			      rst,

    input [OPTION_OPERAND_WIDTH-1:0]  virt_addr_i,
    input [OPTION_OPERAND_WIDTH-1:0]  virt_addr_match_i,
    output [OPTION_OPERAND_WIDTH-1:0] phys_addr_o,
    output 			      cache_inhibit_o,

    input 			      supervisor_mode_i,

    output 			      tlb_miss_o,
    output 			      pagefault_o,

    // SPR interface
    input [15:0] 		      spr_bus_addr_i,
    input 			      spr_bus_we_i,
    input 			      spr_bus_stb_i,
    input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_i,

    output [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o,
    output 			      spr_bus_ack_o
    );

   wire [OPTION_OPERAND_WIDTH-1:0]    itlb_match_dout;
   wire [OPTION_IMMU_SET_WIDTH-1:0]   itlb_match_addr;

   wire [OPTION_OPERAND_WIDTH-1:0]    itlb_trans_dout;
   wire [OPTION_IMMU_SET_WIDTH-1:0]   itlb_trans_addr;

   wire [OPTION_IMMU_SET_WIDTH-1:0]   itlb_match_spr_addr;
   wire [OPTION_OPERAND_WIDTH-1:0]    itlb_match_spr_dout;
   wire [OPTION_OPERAND_WIDTH-1:0]    itlb_match_spr_din;
   wire 			      itlb_match_spr_we;

   wire [OPTION_IMMU_SET_WIDTH-1:0]   itlb_trans_spr_addr;
   wire [OPTION_OPERAND_WIDTH-1:0]    itlb_trans_spr_dout;
   wire [OPTION_OPERAND_WIDTH-1:0]    itlb_trans_spr_din;
   wire 			      itlb_trans_spr_we;

   wire 			      itlb_match_spr_cs;
   reg 				      itlb_match_spr_cs_r;
   wire 			      itlb_trans_spr_cs;

   // sxe: supervisor execute enable
   // uxe: user exexute enable
   wire 			      sxe;
   wire 			      uxe;

   reg 				      spr_bus_ack;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_bus_ack <= 0;
     else if (itlb_match_spr_cs | itlb_trans_spr_cs)
       spr_bus_ack <= 1;
     else
       spr_bus_ack <= 0;

   assign spr_bus_ack_o = spr_bus_ack & (itlb_match_spr_cs | itlb_trans_spr_cs);

   assign cache_inhibit_o = itlb_trans_dout[1];
   assign sxe = itlb_trans_dout[6];
   assign uxe = itlb_trans_dout[7];

   assign pagefault_o = supervisor_mode_i ? !sxe : !uxe;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       itlb_match_spr_cs_r <= 0;
     else
       itlb_match_spr_cs_r <= itlb_match_spr_cs;

   // TODO: optimize this
   assign itlb_match_spr_cs = spr_bus_stb_i &
			      (spr_bus_addr_i >= `OR1K_SPR_ITLBW0MR0_ADDR) &
			      (spr_bus_addr_i < `OR1K_SPR_ITLBW0TR0_ADDR);
   assign itlb_trans_spr_cs = spr_bus_stb_i &
			      (spr_bus_addr_i >= `OR1K_SPR_ITLBW0TR0_ADDR) &
			      (spr_bus_addr_i < `OR1K_SPR_ITLBW1MR0_ADDR);

   assign itlb_match_addr = virt_addr_i[13+(OPTION_IMMU_SET_WIDTH-1):13];
   assign itlb_trans_addr = virt_addr_i[13+(OPTION_IMMU_SET_WIDTH-1):13];

   assign itlb_match_spr_addr = spr_bus_addr_i[OPTION_IMMU_SET_WIDTH-1:0];
   assign itlb_trans_spr_addr = spr_bus_addr_i[OPTION_IMMU_SET_WIDTH-1:0];

   assign itlb_match_spr_we = itlb_match_spr_cs & spr_bus_we_i;
   assign itlb_trans_spr_we = itlb_trans_spr_cs & spr_bus_we_i;

   assign itlb_match_spr_din = spr_bus_dat_i;
   assign itlb_trans_spr_din = spr_bus_dat_i;

   assign spr_bus_dat_o = itlb_match_spr_cs_r ?
			  itlb_match_spr_dout : itlb_trans_spr_dout;

   assign tlb_miss_o = itlb_match_dout[31:13] != virt_addr_match_i[31:13] |
		       !itlb_match_dout[0]; // valid bit

   assign phys_addr_o = {itlb_trans_dout[31:13], virt_addr_match_i[12:0]};

   // ITLB match registers
   /* mor1kx_true_dpram_sclk AUTO_TEMPLATE (
      // Outputs
      .dout_a			(itlb_match_dout),
      .dout_b			(itlb_match_spr_dout),
      // Inputs
      .addr_a			(itlb_match_addr),
      .we_a			(1'b0),
      .din_a			(0),
      .addr_b			(itlb_match_spr_addr),
      .we_b			(itlb_match_spr_we),
      .din_b			(itlb_match_spr_din),
    );
    */
   mor1kx_true_dpram_sclk
     #(
       .ADDR_WIDTH(OPTION_IMMU_SET_WIDTH),
       .DATA_WIDTH(OPTION_OPERAND_WIDTH)
       )
   itlb_match_regs
     (/*AUTOINST*/
      // Outputs
      .dout_a				(itlb_match_dout),	 // Templated
      .dout_b				(itlb_match_spr_dout),	 // Templated
      // Inputs
      .clk				(clk),
      .addr_a				(itlb_match_addr),	 // Templated
      .we_a				(1'b0),			 // Templated
      .din_a				(0),			 // Templated
      .addr_b				(itlb_match_spr_addr),	 // Templated
      .we_b				(itlb_match_spr_we),	 // Templated
      .din_b				(itlb_match_spr_din));	 // Templated


   // ITLB translate registers
   /* mor1kx_true_dpram_sclk AUTO_TEMPLATE (
      // Outputs
      .dout_a			(itlb_trans_dout),
      .dout_b			(itlb_trans_spr_dout),
      // Inputs
      .addr_a			(itlb_trans_addr),
      .we_a			(1'b0),
      .din_a			(0),
      .addr_b			(itlb_trans_spr_addr),
      .we_b			(itlb_trans_spr_we),
      .din_b			(itlb_trans_spr_din),
    );
    */
   mor1kx_true_dpram_sclk
     #(
       .ADDR_WIDTH(OPTION_IMMU_SET_WIDTH),
       .DATA_WIDTH(OPTION_OPERAND_WIDTH)
       )
   itlb_translate_regs
     (/*AUTOINST*/
      // Outputs
      .dout_a				(itlb_trans_dout),	 // Templated
      .dout_b				(itlb_trans_spr_dout),	 // Templated
      // Inputs
      .clk				(clk),
      .addr_a				(itlb_trans_addr),	 // Templated
      .we_a				(1'b0),			 // Templated
      .din_a				(0),			 // Templated
      .addr_b				(itlb_trans_spr_addr),	 // Templated
      .we_b				(itlb_trans_spr_we),	 // Templated
      .din_b				(itlb_trans_spr_din));	 // Templated

endmodule
