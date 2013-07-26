/******************************************************************************
 This Source Code Form is subject to the terms of the
 Open Hardware Description License, v. 1.0. If a copy
 of the OHDL was not distributed with this file, You
 can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

 Description: Data MMU implementation

 Copyright (C) 2013 Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>

 ******************************************************************************/

`include "mor1kx-defines.v"

module mor1kx_dmmu
  #(
    parameter OPTION_OPERAND_WIDTH = 32,
    parameter OPTION_DMMU_SET_WIDTH = 6,
    parameter OPTION_DMMU_WAYS = 1
    )
   (
    input 				  clk,
    input 				  rst,

    input [OPTION_OPERAND_WIDTH-1:0] 	  virt_addr_i,
    input [OPTION_OPERAND_WIDTH-1:0] 	  virt_addr_match_i,
    output [OPTION_OPERAND_WIDTH-1:0] 	  phys_addr_o,
    output 				  cache_inhibit_o,

    input 				  op_store_i,
    input 				  op_load_i,
    input 				  supervisor_mode_i,

    output 				  tlb_miss_o,
    output 				  pagefault_o,

    // SPR interface
    input [15:0] 			  spr_bus_addr_i,
    input 				  spr_bus_we_i,
    input 				  spr_bus_stb_i,
    input [OPTION_OPERAND_WIDTH-1:0] 	  spr_bus_dat_i,

    output [OPTION_OPERAND_WIDTH-1:0] 	  spr_bus_dat_o,
    output 				  spr_bus_ack_o
    );

   wire [OPTION_OPERAND_WIDTH-1:0]    dtlb_match_dout;
   wire [OPTION_DMMU_SET_WIDTH-1:0]   dtlb_match_addr;
   wire 			      dtlb_match_we;
   wire [OPTION_OPERAND_WIDTH-1:0]    dtlb_match_din;

   wire [OPTION_OPERAND_WIDTH-1:0]    dtlb_trans_dout;
   wire [OPTION_DMMU_SET_WIDTH-1:0]   dtlb_trans_addr;
   wire 			      dtlb_trans_we;
   wire [OPTION_OPERAND_WIDTH-1:0]    dtlb_trans_din;

   wire 			      dtlb_match_spr_cs;
   reg 				      dtlb_match_spr_cs_r;
   wire 			      dtlb_trans_spr_cs;
   reg 				      dtlb_trans_spr_cs_r;

   // ure: user read enable
   // uwe: user write enable
   // sre: supervisor read enable
   // swe: supervisor write enable
   wire 			      ure;
   wire 			      uwe;
   wire 			      sre;
   wire 			      swe;

   reg 				      spr_bus_ack;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_bus_ack <= 0;
     else if (spr_bus_stb_i & spr_bus_addr_i[15:11] == 5'd1)
       spr_bus_ack <= 1;
     else
       spr_bus_ack <= 0;

   assign spr_bus_ack_o = spr_bus_ack & spr_bus_stb_i &
			  spr_bus_addr_i[15:11] == 5'd1;

   assign cache_inhibit_o = dtlb_trans_dout[1];
   assign ure = dtlb_trans_dout[6];
   assign uwe = dtlb_trans_dout[7];
   assign sre = dtlb_trans_dout[8];
   assign swe = dtlb_trans_dout[9];

   assign pagefault_o = supervisor_mode_i ?
			!swe & op_store_i || !sre & op_load_i :
			!uwe & op_store_i || !ure & op_load_i;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	dtlb_match_spr_cs_r <= 0;
	dtlb_trans_spr_cs_r <= 0;
     end else begin
	dtlb_match_spr_cs_r <= dtlb_match_spr_cs;
	dtlb_trans_spr_cs_r <= dtlb_trans_spr_cs;
     end

   // TODO: optimize this
   assign dtlb_match_spr_cs = spr_bus_stb_i &
			      (spr_bus_addr_i >= `OR1K_SPR_DTLBW0MR0_ADDR) &
			      (spr_bus_addr_i < `OR1K_SPR_DTLBW0TR0_ADDR);
   assign dtlb_trans_spr_cs = spr_bus_stb_i &
			      (spr_bus_addr_i >= `OR1K_SPR_DTLBW0TR0_ADDR) &
			      (spr_bus_addr_i < `OR1K_SPR_DTLBW1MR0_ADDR);

   assign dtlb_match_addr = dtlb_match_spr_cs ?
			    spr_bus_addr_i[OPTION_DMMU_SET_WIDTH-1:0] :
			    virt_addr_i[13+(OPTION_DMMU_SET_WIDTH-1):13];

   assign dtlb_trans_addr = dtlb_trans_spr_cs ?
			    spr_bus_addr_i[OPTION_DMMU_SET_WIDTH-1:0] :
			    virt_addr_i[13+(OPTION_DMMU_SET_WIDTH-1):13];

   assign dtlb_match_we = dtlb_match_spr_cs & spr_bus_we_i;
   assign dtlb_trans_we = dtlb_trans_spr_cs & spr_bus_we_i;

   assign dtlb_match_din = spr_bus_dat_i;
   assign dtlb_trans_din = spr_bus_dat_i;

   assign spr_bus_dat_o = dtlb_match_spr_cs_r ? dtlb_match_dout :
			  dtlb_trans_spr_cs_r ? dtlb_trans_dout : 0;

   assign tlb_miss_o = dtlb_match_dout[31:13] != virt_addr_match_i[31:13] |
		       !dtlb_match_dout[0]; // valid bit

   assign phys_addr_o = {dtlb_trans_dout[31:13], virt_addr_match_i[12:0]};

   // DTLB match registers
   /* mor1kx_simple_dpram_sclk AUTO_TEMPLATE (
      // Outputs
      .dout			(dtlb_match_dout),
      // Inputs
      .raddr			(dtlb_match_addr),
      .waddr			(dtlb_match_addr),
      .we			(dtlb_match_we),
      .din			(dtlb_match_din),
    );
    */
   mor1kx_simple_dpram_sclk
     #(
       .ADDR_WIDTH(OPTION_DMMU_SET_WIDTH),
       .DATA_WIDTH(OPTION_OPERAND_WIDTH),
       .ENABLE_BYPASS("FALSE")
       )
   dtlb_match_regs
     (/*AUTOINST*/
      // Outputs
      .dout				(dtlb_match_dout),	 // Templated
      // Inputs
      .clk				(clk),
      .raddr				(dtlb_match_addr),	 // Templated
      .waddr				(dtlb_match_addr),	 // Templated
      .we				(dtlb_match_we),	 // Templated
      .din				(dtlb_match_din));	 // Templated


   // DTLB translate registers
   /* mor1kx_simple_dpram_sclk AUTO_TEMPLATE (
      // Outputs
      .dout			(dtlb_trans_dout),
      // Inputs
      .raddr			(dtlb_trans_addr),
      .waddr			(dtlb_trans_addr),
      .we			(dtlb_trans_we),
      .din			(dtlb_trans_din),
    );
    */
   mor1kx_simple_dpram_sclk
     #(
       .ADDR_WIDTH(OPTION_DMMU_SET_WIDTH),
       .DATA_WIDTH(OPTION_OPERAND_WIDTH),
       .ENABLE_BYPASS("FALSE")
       )
   dtlb_translate_regs
     (/*AUTOINST*/
      // Outputs
      .dout				(dtlb_trans_dout),	 // Templated
      // Inputs
      .clk				(clk),
      .raddr				(dtlb_trans_addr),	 // Templated
      .waddr				(dtlb_trans_addr),	 // Templated
      .we				(dtlb_trans_we),	 // Templated
      .din				(dtlb_trans_din));	 // Templated

endmodule // mor1kx_dmmu
