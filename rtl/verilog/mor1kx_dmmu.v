/* ****************************************************************************
  This source describes Open Hardware and is licensed under the CERN-OHLW v2

  You may redistribute and modify this documentation and make products
  using it under the terms of the CERN-OHL-W v2 (https:/cern.ch/cern-ohl).
  This documentation is distributed WITHOUT ANY EXPRESS OR IMPLIED
  WARRANTY, INCLUDING OF MERCHANTABILITY, SATISFACTORY QUALITY
  AND FITNESS FOR A PARTICULAR PURPOSE. Please see the CERN-OHL-W v2
  for applicable conditions.

  Description: Data MMU implementation

  Copyright (C) 2013 Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>

 ******************************************************************************/

`include "mor1kx-defines.v"

module mor1kx_dmmu
  #(
    parameter FEATURE_DMMU_HW_TLB_RELOAD = "NONE",
    parameter OPTION_OPERAND_WIDTH = 32,
    parameter OPTION_DMMU_SET_WIDTH = 6,
    parameter OPTION_DMMU_WAYS = 1
    )
   (
    input 				  clk,
    input 				  rst,

    input 				  enable_i,
    input [OPTION_OPERAND_WIDTH-1:0] 	  virt_addr_i,
    input [OPTION_OPERAND_WIDTH-1:0] 	  virt_addr_match_i,
    output reg [OPTION_OPERAND_WIDTH-1:0] phys_addr_o,
    output reg                            cache_inhibit_o,

    input 				  op_store_i,
    input 				  op_load_i,
    input 				  supervisor_mode_i,

    output reg                            tlb_miss_o,
    output                                pagefault_o,

    output reg 				  tlb_reload_req_o,
    output 				  tlb_reload_busy_o,
    input 				  tlb_reload_ack_i,
    output reg [OPTION_OPERAND_WIDTH-1:0] tlb_reload_addr_o,
    input [OPTION_OPERAND_WIDTH-1:0] 	  tlb_reload_data_i,
    output 				  tlb_reload_pagefault_o,
    input 				  tlb_reload_pagefault_clear_i,

    // SPR interface
    input [15:0] 			  spr_bus_addr_i,
    input 				  spr_bus_we_i,
    input 				  spr_bus_stb_i,
    input [OPTION_OPERAND_WIDTH-1:0] 	  spr_bus_dat_i,

    output [OPTION_OPERAND_WIDTH-1:0] 	  spr_bus_dat_o,
    output 				  spr_bus_ack_o
    );

   localparam WAYS_WIDTH = (OPTION_DMMU_WAYS < 2) ? 1 : 2;

   wire [OPTION_OPERAND_WIDTH-1:0]    dtlb_match_dout[OPTION_DMMU_WAYS-1:0];
   wire [OPTION_DMMU_SET_WIDTH-1:0]   dtlb_match_addr;
   reg [OPTION_DMMU_WAYS-1:0]         dtlb_match_we;
   wire [OPTION_OPERAND_WIDTH-1:0]    dtlb_match_din;

   wire [OPTION_OPERAND_WIDTH-1:0]    dtlb_match_huge_dout[OPTION_DMMU_WAYS-1:0];
   wire [OPTION_DMMU_SET_WIDTH-1:0]   dtlb_match_huge_addr;
   wire				      dtlb_match_huge_we;

   wire [OPTION_OPERAND_WIDTH-1:0]    dtlb_trans_dout[OPTION_DMMU_WAYS-1:0];
   wire [OPTION_DMMU_SET_WIDTH-1:0]   dtlb_trans_addr;
   reg [OPTION_DMMU_WAYS-1:0]         dtlb_trans_we;
   wire [OPTION_OPERAND_WIDTH-1:0]    dtlb_trans_din;

   wire [OPTION_OPERAND_WIDTH-1:0]    dtlb_trans_huge_dout[OPTION_DMMU_WAYS-1:0];
   wire [OPTION_DMMU_SET_WIDTH-1:0]   dtlb_trans_huge_addr;
   wire				      dtlb_trans_huge_we;

   reg 				      dtlb_match_reload_we;
   reg [OPTION_OPERAND_WIDTH-1:0]     dtlb_match_reload_din;

   reg 				      dtlb_trans_reload_we;
   reg [OPTION_OPERAND_WIDTH-1:0]     dtlb_trans_reload_din;

   wire 			      dtlb_match_spr_cs;
   reg 				      dtlb_match_spr_cs_r;
   wire 			      dtlb_trans_spr_cs;
   reg 				      dtlb_trans_spr_cs_r;

   wire 			      dmmucr_spr_cs;
   reg 				      dmmucr_spr_cs_r;
   reg [OPTION_OPERAND_WIDTH-1:0]     dmmucr;

   wire [1:0] 			      spr_way_idx_full;
   wire [WAYS_WIDTH-1:0] 	      spr_way_idx;
   reg [WAYS_WIDTH-1:0] 	      spr_way_idx_r;

   wire [OPTION_DMMU_WAYS-1:0]        way_huge;

   wire [OPTION_DMMU_WAYS-1:0]        way_hit;
   wire [OPTION_DMMU_WAYS-1:0]        way_huge_hit;

   reg 				      tlb_reload_pagefault;
   reg 				      tlb_reload_huge;

   // ure: user read enable
   // uwe: user write enable
   // sre: supervisor read enable
   // swe: supervisor write enable
   reg                                ure;
   reg                                uwe;
   reg                                sre;
   reg                                swe;

   reg 				      spr_bus_ack;

   genvar                             i;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_bus_ack <= 0;
     else if (spr_bus_stb_i & spr_bus_addr_i[15:11] == 5'd1)
       spr_bus_ack <= 1;
     else
       spr_bus_ack <= 0;

   assign spr_bus_ack_o = spr_bus_ack & spr_bus_stb_i &
			  spr_bus_addr_i[15:11] == 5'd1;

generate
for (i = 0; i < OPTION_DMMU_WAYS; i=i+1) begin : ways
   assign way_huge[i] = &dtlb_match_huge_dout[i][1:0]; // huge & valid

   assign way_hit[i] = (dtlb_match_dout[i][31:13] == virt_addr_match_i[31:13]) &
                       dtlb_match_dout[i][0];  // valid bit

   assign way_huge_hit[i] = (dtlb_match_huge_dout[i][31:24] ==
                             virt_addr_match_i[31:24]) &
                            dtlb_match_huge_dout[i][0];
end
endgenerate

   integer j;
   always @(*) begin
      tlb_miss_o = !tlb_reload_pagefault;
      phys_addr_o = {OPTION_OPERAND_WIDTH{1'b0}};
      phys_addr_o[23:0] = virt_addr_match_i[23:0];
      ure = 0;
      uwe = 0;
      sre = 0;
      swe = 0;
      cache_inhibit_o = 0;

      for (j = 0; j < OPTION_DMMU_WAYS; j=j+1) begin
         if (way_huge[j] & way_huge_hit[j] | !way_huge[j] & way_hit[j])
            tlb_miss_o = 0;

         if (way_huge[j] & way_huge_hit[j]) begin
            phys_addr_o = {dtlb_trans_huge_dout[j][31:24], virt_addr_match_i[23:0]};
            ure = dtlb_trans_huge_dout[j][6];
            uwe = dtlb_trans_huge_dout[j][7];
            sre = dtlb_trans_huge_dout[j][8];
            swe = dtlb_trans_huge_dout[j][9];
            cache_inhibit_o = dtlb_trans_huge_dout[j][1];
         end else if (!way_huge[j] & way_hit[j])begin
            phys_addr_o = {dtlb_trans_dout[j][31:13], virt_addr_match_i[12:0]};
            ure = dtlb_trans_dout[j][6];
            uwe = dtlb_trans_dout[j][7];
            sre = dtlb_trans_dout[j][8];
            swe = dtlb_trans_dout[j][9];
            cache_inhibit_o = dtlb_trans_dout[j][1];
         end

         dtlb_match_we[j] = 0;
         if (dtlb_match_reload_we)
           dtlb_match_we[j] = 1;
         if (j[WAYS_WIDTH-1:0] == spr_way_idx)
           dtlb_match_we[j] = dtlb_match_spr_cs & spr_bus_we_i;

         dtlb_trans_we[j] = 0;
         if (dtlb_trans_reload_we)
           dtlb_trans_we[j] = 1;
         if (j[WAYS_WIDTH-1:0] == spr_way_idx)
           dtlb_trans_we[j] = dtlb_trans_spr_cs & spr_bus_we_i;
      end
   end

   assign pagefault_o = (supervisor_mode_i ?
			!swe & op_store_i || !sre & op_load_i :
			!uwe & op_store_i || !ure & op_load_i) &
			!tlb_reload_busy_o;

   assign spr_way_idx_full = {spr_bus_addr_i[10], spr_bus_addr_i[8]};
   assign spr_way_idx = spr_way_idx_full[WAYS_WIDTH-1:0];

   always @(posedge clk `OR_ASYNC_RST)
     if (rst) begin
	dtlb_match_spr_cs_r <= 0;
	dtlb_trans_spr_cs_r <= 0;
	dmmucr_spr_cs_r <= 0;
        spr_way_idx_r <= 0;
     end else begin
	dtlb_match_spr_cs_r <= dtlb_match_spr_cs;
	dtlb_trans_spr_cs_r <= dtlb_trans_spr_cs;
	dmmucr_spr_cs_r <= dmmucr_spr_cs;
        spr_way_idx_r <= spr_way_idx;
     end

generate /* verilator lint_off WIDTH */
if (FEATURE_DMMU_HW_TLB_RELOAD == "ENABLED") begin
/* verilator lint_on WIDTH */
   assign dmmucr_spr_cs = spr_bus_stb_i &
			  spr_bus_addr_i == `OR1K_SPR_DMMUCR_ADDR;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       dmmucr <= 0;
     else if (dmmucr_spr_cs & spr_bus_we_i)
       dmmucr <= spr_bus_dat_i;

end else begin
   assign dmmucr_spr_cs = 0;
   always @(posedge clk)
     dmmucr <= 0;
end
endgenerate

   assign dtlb_match_spr_cs = spr_bus_stb_i & (spr_bus_addr_i[15:11] == 5'd1) &
                              |spr_bus_addr_i[10:9] & !spr_bus_addr_i[7];
   assign dtlb_trans_spr_cs = spr_bus_stb_i & (spr_bus_addr_i[15:11] == 5'd1) &
                              |spr_bus_addr_i[10:9] & spr_bus_addr_i[7];

   assign dtlb_match_addr = dtlb_match_spr_cs ?
			    spr_bus_addr_i[OPTION_DMMU_SET_WIDTH-1:0] :
			    virt_addr_i[13+(OPTION_DMMU_SET_WIDTH-1):13];
   assign dtlb_trans_addr = dtlb_trans_spr_cs ?
			    spr_bus_addr_i[OPTION_DMMU_SET_WIDTH-1:0] :
			    virt_addr_i[13+(OPTION_DMMU_SET_WIDTH-1):13];

   assign dtlb_match_din = dtlb_match_reload_we ? dtlb_match_reload_din :
			   spr_bus_dat_i;
   assign dtlb_trans_din = dtlb_trans_reload_we ? dtlb_trans_reload_din :
			   spr_bus_dat_i;

   assign dtlb_match_huge_addr = virt_addr_i[24+(OPTION_DMMU_SET_WIDTH-1):24];
   assign dtlb_trans_huge_addr = virt_addr_i[24+(OPTION_DMMU_SET_WIDTH-1):24];

   assign dtlb_match_huge_we = dtlb_match_reload_we & tlb_reload_huge;
   assign dtlb_trans_huge_we = dtlb_trans_reload_we & tlb_reload_huge;

   assign spr_bus_dat_o = dtlb_match_spr_cs_r ? dtlb_match_dout[spr_way_idx_r] :
			  dtlb_trans_spr_cs_r ? dtlb_trans_dout[spr_way_idx_r] :
			  dmmucr_spr_cs_r ? dmmucr : 0;

   localparam TLB_IDLE		 	= 2'd0;
   localparam TLB_GET_PTE_POINTER	= 2'd1;
   localparam TLB_GET_PTE		= 2'd2;
   localparam TLB_READ			= 2'd3;

generate /* verilator lint_off WIDTH */
if (FEATURE_DMMU_HW_TLB_RELOAD == "ENABLED") begin
   /* verilator lint_on WIDTH */

   // Hardware TLB reload
   // Compliant with the suggestion outlined in this thread:
   // http://lists.openrisc.net/pipermail/openrisc/2013-July/001806.html
   //
   // PTE layout:
   // | 31 ... 13 | 12 |  11  |   10  | 9 | 8 | 7 | 6 | 5 | 4 | 3 | 2 | 1 | 0 |
   // |    PPN    | Reserved  |PRESENT| L | X | W | U | D | A |WOM|WBC|CI |CC |
   //
   // Where X/W/U maps into SWE/SRE/UWE/URE like this:
   // X | W | U    SWE | SRE | UWE | URE
   // ----------   ---------------------
   // x | 0 | 0  =  0  |  1  |  0  |  0
   // x | 0 | 1  =  0  |  1  |  0  |  1
   // x | 1 | 0  =  1  |  1  |  0  |  0
   // x | 1 | 1  =  1  |  1  |  1  |  1



   reg [1:0] tlb_reload_state = TLB_IDLE;
   wire      do_reload;

   assign do_reload = enable_i & tlb_miss_o & (dmmucr[31:10] != 0) &
		      (op_load_i | op_store_i);

   assign tlb_reload_busy_o = enable_i & (tlb_reload_state != TLB_IDLE) | do_reload;

   assign tlb_reload_pagefault_o = tlb_reload_pagefault &
				    !tlb_reload_pagefault_clear_i;

   always @(posedge clk) begin
      if (tlb_reload_pagefault_clear_i)
	tlb_reload_pagefault <= 0;
      dtlb_trans_reload_we <= 0;
      dtlb_trans_reload_din <= 0;
      dtlb_match_reload_we <= 0;
      dtlb_match_reload_din <= 0;

      case (tlb_reload_state)
	TLB_IDLE: begin
	   tlb_reload_huge <= 0;
	   tlb_reload_req_o <= 0;
	   if (do_reload) begin
	      tlb_reload_req_o <= 1;
	      tlb_reload_addr_o <= {dmmucr[31:10],
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
		 dtlb_trans_reload_din[31:13] <= tlb_reload_data_i[31:13];
		 // SWE = W
		 dtlb_trans_reload_din[9] <= tlb_reload_data_i[7];
		 // SRE = 1
		 dtlb_trans_reload_din[8] <= 1'b1;
		 // UWE = W & U
		 dtlb_trans_reload_din[7] <= tlb_reload_data_i[7] &
					      tlb_reload_data_i[6];
		 // URE = U
		 dtlb_trans_reload_din[6] <= tlb_reload_data_i[6];
		 // Dirty, Accessed, Weakly-Ordered-Memory, Writeback cache,
		 // Cache inhibit, Cache coherent
		 dtlb_trans_reload_din[5:0] <= tlb_reload_data_i[5:0];
		 dtlb_trans_reload_we <= 1;

		 // Match register generation.
		 // VPN
		 dtlb_match_reload_din[31:13] <= virt_addr_match_i[31:13];
		 // Valid
		 dtlb_match_reload_din[0] <= 1;
		 dtlb_match_reload_we <= 1;

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

      // Abort if enable deasserts in the middle of a reload
      if (!enable_i | (dmmucr[31:10] == 0))
	tlb_reload_state <= TLB_IDLE;

   end
end else begin // if (FEATURE_DMMU_HW_TLB_RELOAD == "ENABLED")
   assign tlb_reload_pagefault_o = 0;
   assign tlb_reload_busy_o = 0;
   always @(posedge clk) begin
      tlb_reload_req_o <= 0;
      tlb_reload_addr_o <= 0;
      tlb_reload_pagefault <= 0;
      dtlb_trans_reload_we <= 0;
      dtlb_trans_reload_din <= 0;
      dtlb_match_reload_we <= 0;
      dtlb_match_reload_din <= 0;
   end
end
endgenerate

generate
for (i = 0; i < OPTION_DMMU_WAYS; i=i+1) begin : dtlb
   // DTLB match registers
   mor1kx_true_dpram_sclk
     #(
       .ADDR_WIDTH(OPTION_DMMU_SET_WIDTH),
       .DATA_WIDTH(OPTION_OPERAND_WIDTH)
       )
   dtlb_match_regs
      (
       // Outputs
       .dout_a (dtlb_match_dout[i]),
       .dout_b (dtlb_match_huge_dout[i]),
       // Inputs
       .clk_a  (clk),
       .addr_a (dtlb_match_addr),
       .we_a   (dtlb_match_we[i]),
       .din_a  (dtlb_match_din),
       .clk_b  (clk),
       .addr_b (dtlb_match_huge_addr),
       .we_b   (dtlb_match_huge_we),
       .din_b  (dtlb_match_reload_din)
       );


   // DTLB translate registers
   mor1kx_true_dpram_sclk
     #(
       .ADDR_WIDTH(OPTION_DMMU_SET_WIDTH),
       .DATA_WIDTH(OPTION_OPERAND_WIDTH)
       )
   dtlb_translate_regs
     (
      // Outputs
      .dout_a (dtlb_trans_dout[i]),
      .dout_b (dtlb_trans_huge_dout[i]),
      // Inputs
      .clk_a  (clk),
      .addr_a (dtlb_trans_addr),
      .we_a   (dtlb_trans_we[i]),
      .din_a  (dtlb_trans_din),
      .clk_b  (clk),
      .addr_b (dtlb_trans_huge_addr),
      .we_b   (dtlb_trans_huge_we),
      .din_b  (dtlb_trans_reload_din)
      );
end
endgenerate

/*-------------------Formal Checking---------------------*/

`ifdef FORMAL

`ifdef DMMU
`define ASSUME assume
`else
`define ASSUME assert
`endif

   reg f_past_valid;
   (* anyconst *) wire [OPTION_OPERAND_WIDTH-1:0] f_vaddr;
   initial f_past_valid = 1'b0;
   initial assume (rst);
   always @(posedge clk)
      f_past_valid <= 1'b1;
   always @(*)
      if (!f_past_valid)
         assume (rst);
      else
         assume (!rst);

   always @(posedge clk) begin
      if (f_past_valid && !$past(rst))
         `ASSUME ($onehot0({op_load_i, op_store_i}));
   end

//------------------DMMU PROPERTIES-------------------

   //Physical Address of f_vaddr virtual address is asserted to verify expected PPN.
   //Case 1: Page bits = 13 bits
   always @(posedge clk) begin
      if ((virt_addr_match_i == f_vaddr) && way_hit[0]
           && !way_huge[0] && !pagefault_o && f_past_valid)
         assert ((phys_addr_o[12:0] == f_vaddr[12:0]) &&
                 phys_addr_o[31:13] == dtlb_trans_dout[0][31:13]);
   end

   //Case 2: Page bits = 24 bits (huge)
   always @(posedge clk) begin
      if ((virt_addr_match_i == f_vaddr) && way_huge_hit[0]
          && way_huge[0] && !pagefault_o && f_past_valid)
         assert ((phys_addr_o[23:0] == f_vaddr[23:0]) &&
                 phys_addr_o[31:24] == dtlb_trans_huge_dout[0][31:24]);
   end

   //On TLB miss, mmu should not inhibit cache.
   always @(*)
      if (tlb_miss_o)
      assert (!cache_inhibit_o);
   always @(*) begin
      assert ($onehot0(way_hit));
      assert ($onehot0(way_huge_hit));
   end

   //On TLB hit, tlb_miss_o should be 0.
   always @(*)
      if (way_huge[0] & way_huge_hit[0] || !way_huge[0] & way_hit[0])
         assert (!tlb_miss_o);

   //DMMU SPR registers are accessible only if the last 5 bits
   // of spr_bus_addr_i corresponds to group 1.
   always @(*)
      if ($onehot(dtlb_match_we) || $onehot(dtlb_trans_we))
         assert (spr_bus_addr_i[15:11] == 5'd1);

   //Spr can't access both Match TLB and Translation TLB at the same time.
   always @(posedge clk)
      if (dtlb_match_spr_cs)
         assert (!dtlb_trans_spr_cs);

   //Disabling Hardware TLB loads dtlb_match_din and dtlb_trans_din
   // with spr_bus_dat_i, so its neccessary to check both match and
   // translate TLBs don't write TLB with same data.
   always @(*)
      if ($onehot(dtlb_match_we))
         assert (!$onehot(dtlb_trans_we));

   //If spr ack is received, assert stb
   always @(posedge clk)
      if (spr_bus_ack_o)
         assert (spr_bus_stb_i);

   //On spr read request, spr write signals shouldn't be generated,
   always @(*)
      if (spr_bus_stb_i && !spr_bus_we_i && spr_bus_addr_i[15:11] == 5'd1)
         assert (!dtlb_trans_we & !dtlb_match_we);

   fspr_slave #(
       .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH),
       .SLAVE("DMMU")
       )
       u_f_dmmu_slave (
        .clk(clk),
        .rst(rst),
         // SPR interface
        .spr_bus_addr_i(spr_bus_addr_i),
        .spr_bus_we_i(spr_bus_we_i),
        .spr_bus_stb_i(spr_bus_stb_i),
        .spr_bus_dat_i(spr_bus_dat_i),
        .spr_bus_dat_o(spr_bus_dat_o),
        .spr_bus_ack_o(spr_bus_ack_o),
        .f_past_valid(f_past_valid)
       );

//----------------Cover------------------

`ifdef DMMU

   always @(posedge clk) begin
      if (f_past_valid && !$past(rst)) begin
         //TLB HIT-------------Trace 0
         cover (!tlb_miss_o && phys_addr_o != 0);
         //Trans write---------Trace 1
         cover (dtlb_trans_spr_cs && $past(dtlb_trans_we)
                && $rose(spr_bus_ack_o));
         //Match write---------Trace 2
         cover (dtlb_match_spr_cs && $past(dtlb_match_we)
                && $rose(spr_bus_ack_o));
      end
   end

`endif

`endif
endmodule // mor1kx_dmmu
