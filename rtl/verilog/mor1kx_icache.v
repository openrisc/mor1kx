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

    input 			      ic_enable,

    input [OPTION_OPERAND_WIDTH-1:0]  pc_addr_i,
    input [OPTION_OPERAND_WIDTH-1:0]  pc_fetch_i,
    input 			      padv_fetch_i,

    // BUS Interface towards CPU
    output 			      cpu_err_o,
    output 			      cpu_ack_o,
    output [31:0] 		      cpu_dat_o,
    input 			      cpu_req_i,

    // BUS Interface towards MEM
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
    output 			      spr_bus_ack_o
    );

   // States
   localparam IDLE		= 5'b00001;
   localparam RESTART		= 5'b00010;
   localparam READ		= 5'b00100;
   localparam REFILL		= 5'b01000;
   localparam INVALIDATE	= 5'b10000;

   // Address space in bytes for a way
   localparam WAY_WIDTH = OPTION_ICACHE_BLOCK_WIDTH + OPTION_ICACHE_SET_WIDTH;
   /*
    * Tag layout
    * +-------------------------------------------------------------+
    * | LRU | wayN valid | wayN index |...| way0 valid | way0 index |
    * +-------------------------------------------------------------+
    */
   localparam TAG_INDEX_WIDTH = (OPTION_ICACHE_LIMIT_WIDTH - WAY_WIDTH);
   localparam TAG_WAY_WIDTH = TAG_INDEX_WIDTH + 1;
   localparam TAG_WAY_VALID = TAG_WAY_WIDTH - 1;
   localparam TAG_WIDTH = TAG_WAY_WIDTH * OPTION_ICACHE_WAYS;
   localparam TAG_LRU = TAG_WIDTH - 1;

   reg 				      ic_enabled;

   // FSM state signals
   reg [4:0] 			      state;
   wire				      idle;
   wire				      read;
   wire				      refill;

   reg 				      cpu_req_r;
   reg 				      cpu_ack;
   wire [31:0] 			      cpu_dat;

   reg [31:0] 			      mem_adr;
   reg 				      mem_req;
   wire [31:0] 			      next_mem_adr;
   reg [OPTION_ICACHE_BLOCK_WIDTH-1:0] start_adr;
   wire 			      refill_done;
   reg 				      refill_match;
   wire				      invalidate;
   wire				      invalidate_edge;
   reg				      invalidate_r;

   reg [OPTION_ICACHE_SET_WIDTH-1:0]  tag_raddr;
   reg [OPTION_ICACHE_SET_WIDTH-1:0]  tag_waddr;
   reg [TAG_WIDTH-1:0]		      tag_din;
   reg 				      tag_we;
   wire [TAG_INDEX_WIDTH-1:0] 	      tag_index;
   wire [TAG_INDEX_WIDTH-1:0] 	      tag_windex;
   wire [TAG_WIDTH-1:0] 	      tag_dout;

   wire [WAY_WIDTH-3:0] 	      way_raddr[OPTION_ICACHE_WAYS-1:0];
   wire [WAY_WIDTH-3:0] 	      way_waddr[OPTION_ICACHE_WAYS-1:0];
   wire [OPTION_OPERAND_WIDTH-1:0]    way_din[OPTION_ICACHE_WAYS-1:0];
   wire [OPTION_OPERAND_WIDTH-1:0]    way_dout[OPTION_ICACHE_WAYS-1:0];
   reg [OPTION_ICACHE_WAYS-1:0]       way_we;

   wire 			      hit;
   wire [OPTION_ICACHE_WAYS-1:0]      way_hit;
   wire 			      lru;

   wire 			      cache_req;

   genvar 			      i;


   // Bypass cache when not enabled and when invalidating
   assign cpu_err_o = ibus_err_i;
   assign cpu_ack_o = (cache_req | refill) ? cpu_ack : ibus_ack_i;
   assign cpu_dat_o = (cache_req) ? cpu_dat : ibus_dat_i;
   assign ibus_adr_o = (cache_req | refill) ? mem_adr : pc_addr_i;
   assign ibus_req_o = (cache_req | refill) ? mem_req : cpu_req_i;

   always @(posedge clk)
     if (invalidate_edge)
       tag_waddr <= spr_bus_dat_i[WAY_WIDTH-1:OPTION_ICACHE_BLOCK_WIDTH];
     else
       tag_waddr <= tag_raddr;

   assign tag_index = pc_fetch_i[OPTION_ICACHE_LIMIT_WIDTH-1:WAY_WIDTH];
   assign tag_windex = mem_adr[OPTION_ICACHE_LIMIT_WIDTH-1:WAY_WIDTH];

   generate
      if (OPTION_ICACHE_WAYS > 2) begin
	 initial begin
	    $display("ERROR: OPTION_ICACHE_WAYS > 2, not supported");
	    $finish();
	 end
      end

      for (i = 0; i < OPTION_ICACHE_WAYS; i=i+1) begin : ways
	 assign way_raddr[i] = padv_fetch_i & (read | idle |
			       refill & cpu_ack_o & ibus_ack_i & refill_done) ?
			       pc_addr_i[WAY_WIDTH-1:2] :
			       pc_fetch_i[WAY_WIDTH-1:2];
	 assign way_waddr[i] = mem_adr[WAY_WIDTH-1:2];
	 assign way_din[i] = ibus_dat_i;
	 /*
	  * compare tag stored index with incoming index
	  * and check valid bit
	  */
	 assign way_hit[i] = tag_dout[(i + 1)*TAG_WAY_VALID] &
			      (tag_dout[((i + 1)*TAG_WAY_WIDTH)-2:
					i*TAG_WAY_WIDTH] == tag_index);
      end
   endgenerate

   assign hit = |way_hit;

   generate
      if (OPTION_ICACHE_LIMIT_WIDTH == OPTION_OPERAND_WIDTH) begin
	 assign cache_req = ic_enabled;
      end else if (OPTION_ICACHE_LIMIT_WIDTH < OPTION_OPERAND_WIDTH) begin
	 assign cache_req = ic_enabled &
			   (pc_addr_i[OPTION_OPERAND_WIDTH-1:
				      OPTION_ICACHE_LIMIT_WIDTH] == 0);
      end else begin
	 initial begin
	    $display("ERROR: OPTION_ICACHE_LIMIT_WIDTH > OPTION_OPERAND_WIDTH");
	    $finish();
	 end
      end
   endgenerate

   generate
      if (OPTION_ICACHE_WAYS == 2) begin
	 assign cpu_dat = refill ? ibus_dat_i :
			  way_hit[0] ? way_dout[0] : way_dout[1];
      end else begin
	 assign cpu_dat = refill ? ibus_dat_i : way_dout[0];
      end
   endgenerate

   assign lru = tag_dout[TAG_LRU];

   assign next_mem_adr = (OPTION_ICACHE_BLOCK_WIDTH == 5) ?
			 {mem_adr[31:5],  mem_adr[4:0] + 5'd4} : // 32 byte
			 {mem_adr[31:4],  mem_adr[3:0] + 4'd4};  // 16 byte

   assign refill_done = (next_mem_adr[OPTION_ICACHE_BLOCK_WIDTH-1:0] ==
			 start_adr);

   assign idle = (state == IDLE);
   assign refill = (state == REFILL);
   assign read = (state == READ);

   /*
    * SPR bus interface
    */
   assign invalidate = spr_bus_stb_i & spr_bus_we_i &
		       (spr_bus_addr_i == `OR1K_SPR_ICBIR_ADDR);

   assign invalidate_edge = invalidate & ~invalidate_r;
   assign spr_bus_ack_o = 1'b1;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       invalidate_r <= 1'b0;
     else
       invalidate_r <= invalidate;

   /*
    * Cache enable logic, wait for accesses to finish before enabling cache
    */
    always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       ic_enabled <= 1; /*SJK*/
     else if (ic_enable & (ibus_ack_i | !cpu_req_i))
       ic_enabled <= 1;
     else if (!ic_enable & idle)
       ic_enabled <= 0;

   wire cpu_req_edge = cpu_req_i & !cpu_req_r;
   always @(posedge clk)
       cpu_req_r <= cpu_req_i;

   /*
    * Cache FSM
    */
   always @(posedge clk `OR_ASYNC_RST) begin
      case (state)
	IDLE: begin
	   if (padv_fetch_i & cache_req & ic_enable) begin
	      state <= READ;
	      mem_adr <= pc_addr_i;
	      start_adr <= pc_addr_i[OPTION_ICACHE_BLOCK_WIDTH-1:0];
	   end
	end

	RESTART: begin
	   mem_adr <= pc_fetch_i;
	   state <= READ;
	end

	READ: begin
	   if (cache_req & ic_enable) begin
	      if (hit) begin
		 state <= READ;
		 mem_adr <= pc_addr_i;
	      end else if (padv_fetch_i) begin
		 start_adr <= pc_fetch_i[OPTION_ICACHE_BLOCK_WIDTH-1:0];
		 mem_adr <= pc_fetch_i;
		 refill_match <= 1'b1;
		 state <= REFILL;
	      end
	   end else begin
	      state <= IDLE;
	   end
	end

	REFILL: begin
	   if (ibus_ack_i) begin
	      mem_adr <= next_mem_adr;

	      if (pc_addr_i == next_mem_adr)
		refill_match <= 1'b1;
	      else
		refill_match <= 1'b0;
	      /*
	       * done refilling, go back to READ
	       * the correct address will be muxed onto
	       * tag/cache memories
	       */
	      if (refill_done)
		state <= READ;
	   end
	   /* prevent acking when no request */
//	   if (!padv_fetch_i)
//	      refill_match <= 1'b0;
	end

	INVALIDATE: begin
	   mem_adr <= pc_fetch_i;
	   state <= RESTART;
	end

	default:
	  state <= IDLE;
      endcase

      if (invalidate_edge)
	 state <= INVALIDATE;

      if (rst | ibus_err_i)
	state <= IDLE;
   end

   always @(*) begin
      cpu_ack = 1'b0;
      mem_req = 1'b0;
      tag_we = 1'b0;
      way_we = {(OPTION_ICACHE_WAYS){1'b0}};
      tag_din = tag_dout;
      if (padv_fetch_i)
	tag_raddr = pc_addr_i[WAY_WIDTH-1:OPTION_ICACHE_BLOCK_WIDTH];
      else
	tag_raddr = pc_fetch_i[WAY_WIDTH-1:OPTION_ICACHE_BLOCK_WIDTH];

      case (state)
	READ: begin
	   if (hit) begin
	      cpu_ack = 1'b1;
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

	RESTART: begin
	   tag_raddr = pc_fetch_i[WAY_WIDTH-1:OPTION_ICACHE_BLOCK_WIDTH];
	end

	REFILL: begin
	   mem_req = 1'b1;
	   tag_raddr = mem_adr[WAY_WIDTH-1:OPTION_ICACHE_BLOCK_WIDTH];
	   if (ibus_ack_i) begin
	      if (OPTION_ICACHE_WAYS == 2) begin
		 if (lru)
		   way_we[1] = 1'b1;
		 else
		   way_we[0] = 1'b1;
	      end else begin
		   way_we[0] = 1'b1;
	      end
	      if (refill_match & ic_enable & (pc_fetch_i == mem_adr))
		 cpu_ack = 1'b1;

	      if (refill_done) begin
		 if (ibus_ack_i & cpu_ack_o & padv_fetch_i)
		     tag_raddr = pc_addr_i[WAY_WIDTH-1:OPTION_ICACHE_BLOCK_WIDTH];
		 else if (ibus_ack_i)
		     tag_raddr = pc_fetch_i[WAY_WIDTH-1:OPTION_ICACHE_BLOCK_WIDTH];

		 if (OPTION_ICACHE_WAYS == 2) begin
		    if (lru) begin // way 1
		       tag_din[TAG_WAY_VALID*2] = 1'b1;
		       tag_din[TAG_LRU] = 1'b0;
		       tag_din[(2*TAG_WAY_WIDTH)-2:TAG_WAY_WIDTH] = tag_windex;
		    end else begin // way0
		       tag_din[TAG_WAY_VALID] = 1'b1;
		       tag_din[TAG_LRU] = 1'b1;
		       tag_din[TAG_WAY_WIDTH-2:0] = tag_windex;
		    end
		 end else begin
		       tag_din[TAG_WAY_VALID] = 1'b1;
		       tag_din[TAG_LRU] = 1'b1;
		       tag_din[TAG_WAY_WIDTH-2:0] = tag_windex;
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
      endcase
   end

   /* mor1kx_spram AUTO_TEMPLATE (
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
	 mor1kx_spram
	       #(
		 .ADDR_WIDTH(WAY_WIDTH-2),
		 .DATA_WIDTH(OPTION_OPERAND_WIDTH)
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

   /* mor1kx_spram AUTO_TEMPLATE (
      // Outputs
      .dout			(tag_dout[TAG_WIDTH-1:0]),
      // Inputs
      .raddr			(tag_raddr),
      .waddr			(tag_waddr),
      .we			(tag_we),
      .din			(tag_din));
    */
   mor1kx_spram
     #(
       .ADDR_WIDTH(OPTION_ICACHE_SET_WIDTH),
       .DATA_WIDTH(TAG_WIDTH)
     )
   tag_ram
     (/*AUTOINST*/
      // Outputs
      .dout				(tag_dout[TAG_WIDTH-1:0]), // Templated
      // Inputs
      .clk				(clk),
      .raddr				(tag_raddr),		 // Templated
      .waddr				(tag_waddr),		 // Templated
      .we				(tag_we),		 // Templated
      .din				(tag_din));		 // Templated

endmodule
