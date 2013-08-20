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
    parameter FEATURE_IMMU_HW_TLB_RELOAD = "NONE",
    parameter OPTION_OPERAND_WIDTH = 32,
    parameter OPTION_IMMU_SET_WIDTH = 6,
    parameter OPTION_IMMU_WAYS = 1
    )
   (
    input 				  clk,
    input 				  rst,

    input 				  enable_i,

    output 				  busy_o,

    input [OPTION_OPERAND_WIDTH-1:0] 	  virt_addr_i,
    input [OPTION_OPERAND_WIDTH-1:0] 	  virt_addr_match_i,
    output [OPTION_OPERAND_WIDTH-1:0] 	  phys_addr_o,
    output 				  cache_inhibit_o,

    input 				  supervisor_mode_i,

    output 				  tlb_miss_o,
    output 				  pagefault_o,

    output reg 				  tlb_reload_req_o,
    input 				  tlb_reload_ack_i,
    output reg [OPTION_OPERAND_WIDTH-1:0] tlb_reload_addr_o,
    input [OPTION_OPERAND_WIDTH-1:0] 	  tlb_reload_data_i,
    output 				  tlb_reload_pagefault_o,
    input 				  tlb_reload_pagefault_clear_i,
    output 				  tlb_reload_busy_o,

    // SPR interface
    input [15:0] 			  spr_bus_addr_i,
    input 				  spr_bus_we_i,
    input 				  spr_bus_stb_i,
    input [OPTION_OPERAND_WIDTH-1:0] 	  spr_bus_dat_i,

    output [OPTION_OPERAND_WIDTH-1:0] 	  spr_bus_dat_o,
    output 				  spr_bus_ack_o
    );

   wire [OPTION_OPERAND_WIDTH-1:0]    itlb_match_dout;
   wire [OPTION_IMMU_SET_WIDTH-1:0]   itlb_match_addr;
   wire				      itlb_match_we;
   wire [OPTION_OPERAND_WIDTH-1:0]    itlb_match_din;

   wire [OPTION_OPERAND_WIDTH-1:0]    itlb_match_huge_dout;
   wire [OPTION_IMMU_SET_WIDTH-1:0]   itlb_match_huge_addr;
   wire				      itlb_match_huge_we;

   wire [OPTION_OPERAND_WIDTH-1:0]    itlb_trans_dout;
   wire [OPTION_IMMU_SET_WIDTH-1:0]   itlb_trans_addr;
   wire				      itlb_trans_we;
   wire [OPTION_OPERAND_WIDTH-1:0]    itlb_trans_din;

   wire [OPTION_OPERAND_WIDTH-1:0]    itlb_trans_huge_dout;
   wire [OPTION_IMMU_SET_WIDTH-1:0]   itlb_trans_huge_addr;
   wire				      itlb_trans_huge_we;

   reg 				      itlb_match_reload_we;
   reg [OPTION_OPERAND_WIDTH-1:0]     itlb_match_reload_din;

   reg 				      itlb_trans_reload_we;
   reg [OPTION_OPERAND_WIDTH-1:0]     itlb_trans_reload_din;

   wire 			      itlb_match_spr_cs;
   reg 				      itlb_match_spr_cs_r;
   wire 			      itlb_trans_spr_cs;
   reg 				      itlb_trans_spr_cs_r;

   wire 			      immucr_spr_cs;
   reg 				      immucr_spr_cs_r;
   reg [OPTION_OPERAND_WIDTH-1:0]     immucr;

   wire				      tlb_huge;

   wire				      tlb_miss;
   wire				      tlb_huge_miss;

   reg 				      tlb_reload_pagefault;
   reg 				      tlb_reload_huge;

   // sxe: supervisor execute enable
   // uxe: user exexute enable
   wire 			      sxe;
   wire 			      uxe;

   reg 				      spr_bus_ack;
   reg 				      spr_bus_ack_r;
   wire [OPTION_OPERAND_WIDTH-1:0]    spr_bus_dat;
   reg [OPTION_OPERAND_WIDTH-1:0]     spr_bus_dat_r;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_bus_ack <= 0;
     else if (spr_bus_stb_i & spr_bus_addr_i[15:11] == 5'd2)
       spr_bus_ack <= 1;
     else
       spr_bus_ack <= 0;

   always @(posedge clk)
     spr_bus_ack_r <= spr_bus_ack;

   always @(posedge clk)
     if (spr_bus_ack & !spr_bus_ack_r)
       spr_bus_dat_r <= spr_bus_dat;

   assign spr_bus_ack_o = spr_bus_ack & spr_bus_stb_i &
			  spr_bus_addr_i[15:11] == 5'd2;

   assign cache_inhibit_o = tlb_huge ? itlb_trans_huge_dout[1] :
			     itlb_trans_dout[1];
   assign sxe = tlb_huge ? itlb_trans_huge_dout[6] : itlb_trans_dout[6];
   assign uxe = tlb_huge ? itlb_trans_huge_dout[7] : itlb_trans_dout[7];

   assign pagefault_o = (supervisor_mode_i ? !sxe : !uxe) &
			!tlb_reload_busy_o & !busy_o;

   assign busy_o = ((itlb_match_spr_cs | itlb_trans_spr_cs) & !spr_bus_ack |
		    (itlb_match_spr_cs_r | itlb_trans_spr_cs_r) &
		    spr_bus_ack & !spr_bus_ack_r) & enable_i;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	itlb_match_spr_cs_r <= 0;
	itlb_trans_spr_cs_r <= 0;
	immucr_spr_cs_r <= 0;
     end else begin
	itlb_match_spr_cs_r <= itlb_match_spr_cs;
	itlb_trans_spr_cs_r <= itlb_trans_spr_cs;
	immucr_spr_cs_r <= immucr_spr_cs;
     end

generate /* verilator lint_off WIDTH */
if (FEATURE_IMMU_HW_TLB_RELOAD == "ENABLED") begin
/* verilator lint_on WIDTH */
   assign immucr_spr_cs = spr_bus_stb_i &
			  spr_bus_addr_i == `OR1K_SPR_IMMUCR_ADDR;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       immucr <= 0;
     else if (immucr_spr_cs & spr_bus_we_i)
       immucr <= spr_bus_dat_i;

end else begin
   assign immucr_spr_cs = 0;
   always @(posedge clk)
     immucr <= 0;
end
endgenerate

   // TODO: optimize this
   assign itlb_match_spr_cs = spr_bus_stb_i &
			      (spr_bus_addr_i >= `OR1K_SPR_ITLBW0MR0_ADDR) &
			      (spr_bus_addr_i < `OR1K_SPR_ITLBW0TR0_ADDR);
   assign itlb_trans_spr_cs = spr_bus_stb_i &
			      (spr_bus_addr_i >= `OR1K_SPR_ITLBW0TR0_ADDR) &
			      (spr_bus_addr_i < `OR1K_SPR_ITLBW1MR0_ADDR);

   assign itlb_match_addr = itlb_match_spr_cs & !spr_bus_ack ?
			    spr_bus_addr_i[OPTION_IMMU_SET_WIDTH-1:0] :
			    virt_addr_i[13+(OPTION_IMMU_SET_WIDTH-1):13];
   assign itlb_trans_addr = itlb_trans_spr_cs & !spr_bus_ack ?
			    spr_bus_addr_i[OPTION_IMMU_SET_WIDTH-1:0] :
			    virt_addr_i[13+(OPTION_IMMU_SET_WIDTH-1):13];

   assign itlb_match_we = itlb_match_spr_cs & spr_bus_we_i & !spr_bus_ack |
			  itlb_match_reload_we & !tlb_reload_huge;
   assign itlb_trans_we = itlb_trans_spr_cs & spr_bus_we_i & !spr_bus_ack |
			  itlb_trans_reload_we & !tlb_reload_huge;
   assign itlb_match_din = itlb_match_spr_cs & spr_bus_we_i & !spr_bus_ack ?
			   spr_bus_dat_i : itlb_match_reload_din;
   assign itlb_trans_din = itlb_trans_spr_cs & spr_bus_we_i & !spr_bus_ack ?
			   spr_bus_dat_i : itlb_trans_reload_din;

   assign itlb_match_huge_addr = virt_addr_i[24+(OPTION_IMMU_SET_WIDTH-1):24];
   assign itlb_trans_huge_addr = virt_addr_i[24+(OPTION_IMMU_SET_WIDTH-1):24];

   assign itlb_match_huge_we = itlb_match_reload_we & tlb_reload_huge;
   assign itlb_trans_huge_we = itlb_trans_reload_we & tlb_reload_huge;

   assign spr_bus_dat = itlb_match_spr_cs_r ? itlb_match_dout :
			itlb_trans_spr_cs_r ? itlb_trans_dout :
			immucr_spr_cs_r ? immucr : 0;

   // Use registered value on all but the first cycle spr_bus_ack is asserted
   assign spr_bus_dat_o = spr_bus_ack & !spr_bus_ack_r ? spr_bus_dat :
			  spr_bus_dat_r;

   assign tlb_huge = &itlb_match_huge_dout[1:0]; // huge & valid

   assign tlb_miss = itlb_match_dout[31:13] != virt_addr_match_i[31:13] |
		     !itlb_match_dout[0];  // valid bit

   assign tlb_huge_miss = itlb_match_huge_dout[31:24] !=
			  virt_addr_match_i[31:24] | !itlb_match_huge_dout[0];

   assign tlb_miss_o = (tlb_miss & !tlb_huge | tlb_huge_miss & tlb_huge) &
		       !tlb_reload_pagefault & !busy_o;

   assign phys_addr_o = tlb_huge ?
			{itlb_trans_huge_dout[31:24], virt_addr_match_i[23:0]} :
			{itlb_trans_dout[31:13], virt_addr_match_i[12:0]};

generate /* verilator lint_off WIDTH */
if (FEATURE_IMMU_HW_TLB_RELOAD == "ENABLED") begin
   /* verilator lint_on WIDTH */

   // Hardware TLB reload
   // Compliant with the suggestions outlined in this thread:
   // http://lists.openrisc.net/pipermail/openrisc/2013-July/001806.html
   //
   // PTE layout:
   // | 31 ... 13 | 12 |  11 |   10  | 9 | 8 | 7 | 6 | 5 | 4 | 3 | 2 | 1 | 0 |
   // |    PPN    | Reserved |PRESENT| L | X | W | U | D | A |WOM|WBC|CI |CC |
   //
   // Where X/W/U maps into SXE/UXE like this:
   // X | W | U   SXE | UXE
   // ---------   ---------
   // 0 | x | 0 =  0  |  0
   // 0 | x | 1 =  0  |  0
   //    ...
   // 1 | x | 0 =  1  |  0
   // 1 | x | 1 =  1  |  1


   localparam TLB_IDLE		 	= 2'd0;
   localparam TLB_GET_PTE_POINTER	= 2'd1;
   localparam TLB_GET_PTE		= 2'd2;
   localparam TLB_READ			= 2'd3;

   reg [1:0] tlb_reload_state = TLB_IDLE;
   wire      do_reload;

   assign do_reload = enable_i & tlb_miss_o & (immucr[31:10] != 0);
   assign tlb_reload_busy_o = (tlb_reload_state != TLB_IDLE) | do_reload;
   assign tlb_reload_pagefault_o = tlb_reload_pagefault &
				    !tlb_reload_pagefault_clear_i;

   always @(posedge clk) begin
      if (tlb_reload_pagefault_clear_i | rst)
	tlb_reload_pagefault <= 0;
      itlb_trans_reload_we <= 0;
      itlb_trans_reload_din <= 0;
      itlb_match_reload_we <= 0;
      itlb_match_reload_din <= 0;

      case (tlb_reload_state)
	TLB_IDLE: begin
	   tlb_reload_huge <= 0;
	   tlb_reload_req_o <= 0;
	   if (do_reload) begin
	      tlb_reload_req_o <= 1;
	      tlb_reload_addr_o <= {immucr[31:10],
				    virt_addr_match_i[31:24], 2'b00};
	      tlb_reload_state <= TLB_GET_PTE_POINTER;
	   end
	end

	//
	// Here we get the pointer to the PTE table, next is to fetch
	// the actual pte from the offset in the table.
	// The offset is calculated by:
	// ((virt_addr_match >> PAGE_BITS) & (PTE_CNT-1)) << 2
	// Where PAGE_BITS is 13 (8 kb page) and PTE_CNT is 2048
	// (number of PTEs in the PTE table)
	//
	TLB_GET_PTE_POINTER: begin
	   tlb_reload_huge <= 0;
	   if (tlb_reload_ack_i) begin
	      if (tlb_reload_data_i[31:13] == 0) begin
		 tlb_reload_pagefault <= 1;
		 tlb_reload_req_o <= 0;
		 tlb_reload_state <= TLB_IDLE;
	      end else if (tlb_reload_data_i[9]) begin
		 tlb_reload_huge <= 1;
		 tlb_reload_req_o <= 0;
		 tlb_reload_state <= TLB_GET_PTE;
	      end else begin
		 tlb_reload_addr_o <= {tlb_reload_data_i[31:13],
				       virt_addr_match_i[23:13], 2'b00};
		 tlb_reload_state <= TLB_GET_PTE;
	      end
	   end
	end

	//
	// Here we get the actual PTE, left to do is to translate the
	// PTE data into our translate and match registers.
	//
	TLB_GET_PTE: begin
	   if (tlb_reload_ack_i) begin
	      tlb_reload_req_o <= 0;
	      // Check PRESENT bit
	      if (!tlb_reload_data_i[10]) begin
		 tlb_reload_pagefault <= 1;
		 tlb_reload_state <= TLB_IDLE;
	      end else begin
		 // Translate register generation.
		 // PPN
		 itlb_trans_reload_din[31:13] <= tlb_reload_data_i[31:13];
		 // UXE = X & U
		 itlb_trans_reload_din[7] <= tlb_reload_data_i[8] &
					      tlb_reload_data_i[6];
		 // SXE = X
		 itlb_trans_reload_din[6] <= tlb_reload_data_i[8];
		 // Dirty, Accessed, Weakly-Ordered-Memory, Writeback cache,
		 // Cache inhibit, Cache coherent
		 itlb_trans_reload_din[5:0] <= tlb_reload_data_i[5:0];
		 itlb_trans_reload_we <= 1;

		 // Match register generation.
		 // VPN
		 itlb_match_reload_din[31:13] <= virt_addr_match_i[31:13];
		 // PL1
		 itlb_match_reload_din[1] <= tlb_reload_huge;
		 // Valid
		 itlb_match_reload_din[0] <= 1;
		 itlb_match_reload_we <= 1;

		 tlb_reload_state <= TLB_READ;
	      end
	   end
	end

	// Let the just written values propagate out on the read ports
	TLB_READ: begin
	   tlb_reload_state <= TLB_IDLE;
	end

	default:
	  tlb_reload_state <= TLB_IDLE;

      endcase
   end
end else begin // if (FEATURE_IMMU_HW_TLB_RELOAD == "ENABLED")
   assign tlb_reload_pagefault_o = 0;
   assign tlb_reload_busy_o = 0;
   always @(posedge clk) begin
      tlb_reload_req_o <= 0;
      tlb_reload_addr_o <= 0;
      tlb_reload_pagefault <= 0;
      itlb_trans_reload_we <= 0;
      itlb_trans_reload_din <= 0;
      itlb_match_reload_we <= 0;
      itlb_match_reload_din <= 0;
   end
end
endgenerate

   // ITLB match registers
   mor1kx_true_dpram_sclk
     #(
       .ADDR_WIDTH(OPTION_IMMU_SET_WIDTH),
       .DATA_WIDTH(OPTION_OPERAND_WIDTH)
       )
   itlb_match_regs
     (
      // Outputs
      .dout_a				(itlb_match_dout),
      .dout_b				(itlb_match_huge_dout),
      // Inputs
      .clk				(clk),
      .addr_a				(itlb_match_addr),
      .we_a				(itlb_match_we),
      .din_a				(itlb_match_din),
      .addr_b				(itlb_match_huge_addr),
      .we_b				(itlb_match_huge_we),
      .din_b				(itlb_match_reload_din)
      );


   // ITLB translate registers
   mor1kx_true_dpram_sclk
     #(
       .ADDR_WIDTH(OPTION_IMMU_SET_WIDTH),
       .DATA_WIDTH(OPTION_OPERAND_WIDTH)
       )
   itlb_translate_regs
     (
      // Outputs
      .dout_a				(itlb_trans_dout),
      .dout_b				(itlb_trans_huge_dout),
      // Inputs
      .clk				(clk),
      .addr_a				(itlb_trans_addr),
      .we_a				(itlb_trans_we),
      .din_a				(itlb_trans_din),
      .addr_b				(itlb_trans_huge_addr),
      .we_b				(itlb_trans_huge_we),
      .din_b				(itlb_trans_reload_din)
      );

endmodule
