/******************************************************************************
 This Source Code Form is subject to the terms of the
 Open Hardware Description License, v. 1.0. If a copy
 of the OHDL was not distributed with this file, You
 can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

 Description: Instruction cache implementation

 Copyright (C) 2012 Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>

 ******************************************************************************/

`include "mor1kx-defines.v"

module mor1kx_icache
  #(
    parameter OPTION_OPERAND_WIDTH = 32,
    parameter OPTION_ICACHE_BLOCK_WIDTH = 5,
    parameter OPTION_ICACHE_SET_WIDTH = 9,
    parameter OPTION_ICACHE_WAYS = 2,
    parameter OPTION_ICACHE_LIMIT_WIDTH = 32
    )
   (
    input 			      clk,
    input 			      rst,

    input 			      ic_access_i,
    output 			      refill_o,
    output 			      refill_done_o,
    output 			      invalidate_o,

    // CPU Interface
    output 			      cpu_err_o,
    output 			      cpu_ack_o,
    output [31:0] 		      cpu_dat_o,
    input [OPTION_OPERAND_WIDTH-1:0]  cpu_adr_i,
    input [OPTION_OPERAND_WIDTH-1:0]  cpu_adr_match_i,
    input 			      cpu_req_i,

    // BUS Interface
    input 			      ibus_err_i,
    input 			      ibus_ack_i,
    input [31:0] 		      ibus_dat_i,
    output [31:0] 		      ibus_adr_o,
    output 			      ibus_req_o,

    // SPR interface
    input [15:0] 		      spr_bus_addr_i,
    input 			      spr_bus_we_i,
    input 			      spr_bus_stb_i,
    input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_i,

    output [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o,
    output reg 			      spr_bus_ack_o
    );

   // States
   localparam IDLE		= 4'b0001;
   localparam READ		= 4'b0010;
   localparam REFILL		= 4'b0100;
   localparam INVALIDATE	= 4'b1000;

   // Address space in bytes for a way
   localparam WAY_WIDTH = OPTION_ICACHE_BLOCK_WIDTH + OPTION_ICACHE_SET_WIDTH;
   /*
    * Tag memory layout
    *            +---------------------------------------------------------+
    * (index) -> | LRU | wayN valid | wayN tag |...| way0 valid | way0 tag |
    *            +---------------------------------------------------------+
    */

   // The tag is the part left of the index
   localparam TAG_WIDTH = (OPTION_ICACHE_LIMIT_WIDTH - WAY_WIDTH);

   // The tag memory contains entries with OPTION_ICACHE_WAYS parts of
   // each TAGMEM_WAY_WIDTH. Each of those is tag and a valid flag.
   localparam TAGMEM_WAY_WIDTH = TAG_WIDTH + 1;
   localparam TAGMEM_WAY_VALID = TAGMEM_WAY_WIDTH;

   // Compute the total sum of the entry elements
   localparam TAGMEM_WIDTH = TAGMEM_WAY_WIDTH * OPTION_ICACHE_WAYS + 1;

   // For convenience we define the position of the LRU in the tag
   // memory entries
   localparam TAG_LRU = TAGMEM_WIDTH - 1;

   // FSM state signals
   reg [3:0] 			      state;
   wire				      idle;
   wire				      read;
   wire				      refill;

   reg [31:0] 			      ibus_adr;
   wire [31:0] 			      next_ibus_adr;
   wire 			      refill_done;
   wire 			      refill_hit;
   reg [(1<<(OPTION_ICACHE_BLOCK_WIDTH-2))-1:0] refill_valid;
   reg [(1<<(OPTION_ICACHE_BLOCK_WIDTH-2))-1:0] refill_valid_r;

   // The index we read and write from tag memory
   wire [OPTION_ICACHE_SET_WIDTH-1:0] tag_rindex;
   wire [OPTION_ICACHE_SET_WIDTH-1:0] tag_windex;

   // The data from the tag memory
   wire [TAGMEM_WIDTH-1:0] 	      tag_dout;

   // The data to the tag memory
   reg [TAGMEM_WIDTH-1:0] 	      tag_din;

   // Whether to write to the tag memory in this cycle
   reg 				      tag_we;

   reg [TAGMEM_WAY_WIDTH-1:0] 	      tag_save_data;

   // This is the tag we need to write to the tag memory during refill
   wire [TAG_WIDTH-1:0] 	      tag_wtag;

   // This is the tag we check against
   wire [TAG_WIDTH-1:0] 	      tag_tag;

   // Access to the way memories
   wire [WAY_WIDTH-3:0] 	      way_raddr[OPTION_ICACHE_WAYS-1:0];
   wire [WAY_WIDTH-3:0] 	      way_waddr[OPTION_ICACHE_WAYS-1:0];
   wire [OPTION_OPERAND_WIDTH-1:0]    way_din[OPTION_ICACHE_WAYS-1:0];
   wire [OPTION_OPERAND_WIDTH-1:0]    way_dout[OPTION_ICACHE_WAYS-1:0];
   reg [OPTION_ICACHE_WAYS-1:0]       way_we;

   // Does any way hit?
   wire 			      hit;
   wire [OPTION_ICACHE_WAYS-1:0]      way_hit;

   // This is the least recently used value before access the memory.
   wire 			      lru;

   // Register that stores the LRU value from lru
   reg 				      tag_save_lru;

   genvar 			      i;

   assign cpu_err_o = ibus_err_i;
   // Allowing (out of the cache line being refilled) accesses during refill
   // exposes a bug somewhere, causing the Linux kernel to end up with a
   // bus error UNHANDLED EXCEPTION.
   // Until that is sorted out, disable it.
   assign cpu_ack_o = (read /*| refill & ic_access_i*/) & hit |
		      refill_hit & ic_access_i;
   assign ibus_adr_o = ibus_adr;
   assign ibus_req_o = refill;

   assign tag_rindex = cpu_adr_i[WAY_WIDTH-1:OPTION_ICACHE_BLOCK_WIDTH];
   /*
    * The tag mem is written during reads to write the lru info and during
    * refill and invalidate
    */
   assign tag_windex = read ?
		       cpu_adr_match_i[WAY_WIDTH-1:OPTION_ICACHE_BLOCK_WIDTH] :
		       ibus_adr[WAY_WIDTH-1:OPTION_ICACHE_BLOCK_WIDTH];
   assign tag_tag = cpu_adr_match_i[OPTION_ICACHE_LIMIT_WIDTH-1:WAY_WIDTH];
   assign tag_wtag = ibus_adr[OPTION_ICACHE_LIMIT_WIDTH-1:WAY_WIDTH];

   generate
      if (OPTION_ICACHE_WAYS > 2) begin
	 initial begin
	    $display("ERROR: OPTION_ICACHE_WAYS > 2, not supported");
	    $finish();
	 end
      end

      for (i = 0; i < OPTION_ICACHE_WAYS; i=i+1) begin : ways
	 assign way_raddr[i] = cpu_adr_i[WAY_WIDTH-1:2];
	 assign way_waddr[i] = ibus_adr[WAY_WIDTH-1:2];
	 assign way_din[i] = ibus_dat_i;

	 // compare stored tag with incoming tag and check valid bit
	 assign way_hit[i] = tag_dout[((i + 1)*TAGMEM_WAY_VALID)-1] &
			      (tag_dout[((i + 1)*TAGMEM_WAY_WIDTH)-2:
					i*TAGMEM_WAY_WIDTH] == tag_tag);
      end
   endgenerate

   assign hit = |way_hit;

   generate
      if (OPTION_ICACHE_WAYS == 2) begin
	 assign cpu_dat_o = way_hit[0] | refill_hit & !tag_save_lru ?
			    way_dout[0] : way_dout[1];
      end else begin
	 assign cpu_dat_o = way_dout[0];
      end
   endgenerate

   assign lru = tag_dout[TAG_LRU];

   assign next_ibus_adr = (OPTION_ICACHE_BLOCK_WIDTH == 5) ?
			  {ibus_adr[31:5], ibus_adr[4:0] + 5'd4} : // 32 byte
			  {ibus_adr[31:4], ibus_adr[3:0] + 4'd4};  // 16 byte

   assign refill_done_o = refill_done;
   assign refill_done = refill_valid[next_ibus_adr[OPTION_ICACHE_BLOCK_WIDTH-1:2]];
   assign refill_hit = refill_valid_r[cpu_adr_match_i[OPTION_ICACHE_BLOCK_WIDTH-1:2]] &
		       cpu_adr_match_i[OPTION_ICACHE_LIMIT_WIDTH-1:
				       OPTION_ICACHE_BLOCK_WIDTH] ==
		       ibus_adr[OPTION_ICACHE_LIMIT_WIDTH-1:
				OPTION_ICACHE_BLOCK_WIDTH] &
		       refill;

   assign idle = (state == IDLE);
   assign refill = (state == REFILL);
   assign read = (state == READ);

   assign refill_o = refill;

   /*
    * SPR bus interface
    */
   assign invalidate_o = spr_bus_stb_i & spr_bus_we_i &
			 (spr_bus_addr_i == `OR1K_SPR_ICBIR_ADDR);

   /*
    * Cache FSM
    */
   always @(posedge clk `OR_ASYNC_RST) begin
      refill_valid_r <= refill_valid;
      spr_bus_ack_o <= 0;
      case (state)
	IDLE: begin
	   ibus_adr <= cpu_adr_i;
	   if (cpu_req_i)
	     state <= READ;
	end

	READ: begin
	   if (ic_access_i) begin
	      if (hit) begin
		 state <= READ;
		 ibus_adr <= cpu_adr_i;
	      end else if (cpu_req_i) begin
		 refill_valid <= 0;
		 refill_valid_r <= 0;
		 ibus_adr <= cpu_adr_match_i;
		 tag_save_lru <= lru;
		 if (OPTION_ICACHE_WAYS == 2) begin
		    if (lru)
		      tag_save_data <= tag_din[TAGMEM_WAY_WIDTH-1:0];
		    else
		      tag_save_data <= tag_din[2*TAGMEM_WAY_WIDTH-1:TAGMEM_WAY_WIDTH];
		 end
		 state <= REFILL;
	      end
	   end else begin
	      state <= IDLE;
	   end
	end

	REFILL: begin
	   if (ibus_ack_i) begin
	      ibus_adr <= next_ibus_adr;
	      refill_valid[ibus_adr[OPTION_ICACHE_BLOCK_WIDTH-1:2]] <= 1;

	      if (refill_done)
		state <= IDLE;
	   end
	end

	INVALIDATE: begin
	   if (!invalidate_o)
	     state <= IDLE;
	   spr_bus_ack_o <= 1;
	end

	default:
	  state <= IDLE;
      endcase

      if (invalidate_o & !refill) begin
	 /* ibus_adr is hijacked as the invalidate address here */
	 ibus_adr <= spr_bus_dat_i;
	 spr_bus_ack_o <= 1;
	 state <= INVALIDATE;
      end

      if (rst | ibus_err_i)
	state <= IDLE;
   end

   always @(*) begin
      tag_we = 1'b0;
      tag_din = tag_dout;
      way_we = {(OPTION_ICACHE_WAYS){1'b0}};

      case (state)
	READ: begin
	   if (hit) begin
	      /* output data and write back tag with LRU info */
	      if (way_hit[0]) begin
		 tag_din[TAG_LRU] = 1'b1;
	      end
	      if (OPTION_ICACHE_WAYS == 2) begin
		 if (way_hit[1]) begin
		    tag_din[TAG_LRU] = 1'b0;
		 end
	      end
	      tag_we = 1'b1;
	   end
	end

	REFILL: begin
	   if (ibus_ack_i) begin
	      if (OPTION_ICACHE_WAYS == 2) begin
		 if (tag_save_lru)
		   way_we[1] = 1'b1;
		 else
		   way_we[0] = 1'b1;
	      end else begin
		 way_we[0] = 1'b1;
	      end

	      /* Invalidate the way on the first write */
	      if (refill_valid == 0) begin
		 if (OPTION_ICACHE_WAYS == 2) begin
		    if (tag_save_lru)
		      tag_din[(2*TAGMEM_WAY_VALID)-1] = 1'b0;
		    else
		      tag_din[TAGMEM_WAY_VALID-1] = 1'b0;
		 end else begin
		    tag_din[TAGMEM_WAY_VALID-1] = 1'b0;
		 end
		 tag_we = 1'b1;
	      end

	      if (refill_done) begin
		 if (OPTION_ICACHE_WAYS == 2) begin
		    if (tag_save_lru) begin // way 1
		       tag_din[(2*TAGMEM_WAY_VALID)-1] = 1'b1;
		       tag_din[TAG_LRU] = 1'b0;
		       tag_din[(2*TAGMEM_WAY_WIDTH)-2:TAGMEM_WAY_WIDTH] = tag_wtag;
		       tag_din[TAGMEM_WAY_WIDTH-1:0] = tag_save_data;
		    end else begin // way0
		       tag_din[TAGMEM_WAY_VALID-1] = 1'b1;
		       tag_din[TAG_LRU] = 1'b1;
		       tag_din[TAGMEM_WAY_WIDTH-2:0] = tag_wtag;
		       tag_din[2*TAGMEM_WAY_WIDTH-1:TAGMEM_WAY_WIDTH] = tag_save_data;
		    end
		 end else begin
		    tag_din[TAGMEM_WAY_VALID-1] = 1'b1;
		    tag_din[TAG_LRU] = 1'b0;
		    tag_din[TAGMEM_WAY_WIDTH-2:0] = tag_wtag;
		 end

		 tag_we = 1'b1;
	      end
	   end
	end

	INVALIDATE: begin
	   // Lazy invalidation, invalidate everything that matches tag address
	   tag_din = 0;
	   tag_we = 1'b1;
	end

	default: begin
	end
      endcase
   end

   /* mor1kx_simple_dpram_sclk AUTO_TEMPLATE (
      // Outputs
      .dout			(way_dout[i][OPTION_OPERAND_WIDTH-1:0]),
      // Inputs
      .raddr			(way_raddr[i][WAY_WIDTH-3:0]),
      .waddr			(way_waddr[i][WAY_WIDTH-3:0]),
      .we			(way_we[i]),
      .din			(way_din[i][31:0]));
    */
   generate
      for (i = 0; i < OPTION_ICACHE_WAYS; i=i+1) begin : way_memories
	 mor1kx_simple_dpram_sclk
	       #(
		 .ADDR_WIDTH(WAY_WIDTH-2),
		 .DATA_WIDTH(OPTION_OPERAND_WIDTH),
		 .ENABLE_BYPASS("FALSE")
		 )
	 way_data_ram
	       (/*AUTOINST*/
		// Outputs
		.dout			(way_dout[i][OPTION_OPERAND_WIDTH-1:0]), // Templated
		// Inputs
		.clk			(clk),
		.raddr			(way_raddr[i][WAY_WIDTH-3:0]), // Templated
		.waddr			(way_waddr[i][WAY_WIDTH-3:0]), // Templated
		.we			(way_we[i]),		 // Templated
		.din			(way_din[i][31:0]));	 // Templated

      end
   endgenerate

   /* mor1kx_simple_dpram_sclk AUTO_TEMPLATE (
      // Outputs
      .dout			(tag_dout[TAGMEM_WIDTH-1:0]),
      // Inputs
      .raddr			(tag_rindex),
      .waddr			(tag_windex),
      .we			(tag_we),
      .din			(tag_din));
    */
   mor1kx_simple_dpram_sclk
     #(
       .ADDR_WIDTH(OPTION_ICACHE_SET_WIDTH),
       .DATA_WIDTH(TAGMEM_WIDTH),
       .ENABLE_BYPASS("FALSE")
     )
   tag_ram
     (/*AUTOINST*/
      // Outputs
      .dout				(tag_dout[TAGMEM_WIDTH-1:0]), // Templated
      // Inputs
      .clk				(clk),
      .raddr				(tag_rindex),		 // Templated
      .waddr				(tag_windex),		 // Templated
      .we				(tag_we),		 // Templated
      .din				(tag_din));		 // Templated

endmodule
