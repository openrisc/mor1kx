/*
 * (C) Copyright 2011, Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>
 */
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

    // BUS Interface towards CPU
    output 			      cpu_err_o,
    output 			      cpu_ack_o,
    output [31:0] 		      cpu_dat_o,
    input [31:0] 		      cpu_adr_i,
    input 			      cpu_req_i,

    // BUS Interface towards MEM
    input 			      ic_err_i,
    input 			      ic_ack_i,
    input [31:0] 		      ic_dat_i,
    output [31:0] 		      ic_adr_o,
    output 			      ic_req_o,

    // SPR interface
    input [15:0] 		      spr_bus_addr_i,
    input 			      spr_bus_we_i,
    input 			      spr_bus_stb_i,
    input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_i,

    output [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o,
    output reg 			      spr_bus_ack_o
    );

   // States
   parameter IDLE	= 3'b001;
   parameter READ	= 3'b010;
   parameter REFILL	= 3'b100;

   // Address space in bytes for a way
   parameter WAY_WIDTH = OPTION_ICACHE_BLOCK_WIDTH + OPTION_ICACHE_SET_WIDTH;
   /*
    * Tag layout
    * +-------------------------------------------------------------+
    * | LRU | wayN valid | wayN index |...| way0 valid | way0 index |
    * +-------------------------------------------------------------+
    */
   parameter TAG_INDEX_WIDTH = (OPTION_ICACHE_LIMIT_WIDTH - WAY_WIDTH);
   parameter TAG_WAY_WIDTH = TAG_INDEX_WIDTH + 1;
   parameter TAG_WAY_VALID = TAG_WAY_WIDTH - 1;
   parameter TAG_WIDTH = TAG_WAY_WIDTH * OPTION_ICACHE_WAYS;
   parameter TAG_LRU = TAG_WIDTH - 1;

   reg 				      ic_enabled;

   // FSM state signals
   reg [2:0] 			      state;
   reg [2:0] 			      next_state;
   wire				      idle;
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
   reg				      invalidating;

   wire [OPTION_ICACHE_SET_WIDTH-1:0] tag_raddr;
   wire [OPTION_ICACHE_SET_WIDTH-1:0] tag_waddr;
   reg [TAG_WIDTH-1:0]		      tag_din;
   reg 				      tag_we;
   wire [TAG_INDEX_WIDTH-1:0] 	      tag_index;
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
   assign cpu_err_o = ic_err_i;
   assign cpu_ack_o = (cache_req | refill) ? cpu_ack : ic_ack_i;
   assign cpu_dat_o = (cache_req) ? cpu_dat : ic_dat_i;
   assign ic_adr_o = (cache_req | refill) ? mem_adr : cpu_adr_i;
   assign ic_req_o = (cache_req | refill) ? mem_req : cpu_req_i;

   assign tag_raddr = idle ?
		      cpu_adr_i[WAY_WIDTH-1:OPTION_ICACHE_BLOCK_WIDTH] :
		      mem_adr[WAY_WIDTH-1:OPTION_ICACHE_BLOCK_WIDTH];
   assign tag_waddr = mem_adr[WAY_WIDTH-1:OPTION_ICACHE_BLOCK_WIDTH];

   assign tag_index = mem_adr[OPTION_ICACHE_LIMIT_WIDTH-1:WAY_WIDTH];

   generate
      if (OPTION_ICACHE_WAYS > 2) begin
	 initial begin
	    $display("ERROR: OPTION_ICACHE_WAYS > 2, not supported");
	    $finish();
	 end
      end

      for (i = 0; i < OPTION_ICACHE_WAYS; i=i+1) begin : ways
	 assign way_raddr[i] = cpu_adr_i[WAY_WIDTH-1:2];
	 assign way_waddr[i] = mem_adr[WAY_WIDTH-1:2];
	 assign way_din[i] = ic_dat_i;
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
	 assign cache_req = ic_enabled & !invalidating;
      end else if (OPTION_ICACHE_LIMIT_WIDTH < OPTION_OPERAND_WIDTH) begin
	 assign cache_req = ic_enabled & !invalidating &
			   (cpu_adr_i[OPTION_OPERAND_WIDTH-1:
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
	 assign cpu_dat = (state == REFILL) ? ic_dat_i :
			  way_hit[0] ? way_dout[0] : way_dout[1];
      end else begin
	 assign cpu_dat = (state == REFILL) ? ic_dat_i : way_dout[0];
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

   /*
    * SPR bus interface
    */
   assign invalidate = spr_bus_stb_i & spr_bus_we_i &
		       (spr_bus_addr_i == `OR1K_SPR_ICBIR_ADDR);

   always @(posedge clk `OR_ASYNC_RST) begin
      if (rst) begin
	 invalidating <= 0;
	 spr_bus_ack_o <= 0;
      end else begin
	 spr_bus_ack_o <= 0;
	 // wait for any ongoing bus accesses to finish
	 // before switching cache back on after invalidating
	 if (invalidate)
	   invalidating <= 1;
	 else if (idle & invalidating & (ic_ack_i | !cpu_req_i))
	   invalidating <= 0;
      end
   end

   /*
    * Cache enable logic, wait for accesses to finish before enabling cache
    */
    always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       ic_enabled <= 0;
     else if (ic_enable & (ic_ack_i | !cpu_req_i))
       ic_enabled <= 1;
     else if (!ic_enable & idle)
       ic_enabled <= 0;

   /*
    * Cache FSM
    */
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       state <= IDLE;
     else
       state <= next_state;

   // Register incoming address in IDLE state and wrap increment it in REFILL
   always @(posedge clk) begin
      if (invalidate) begin
	 // Load address to invalidate from SPR bus
	 mem_adr <= spr_bus_dat_i;
      end else if (idle & !invalidating) begin
	 start_adr <= cpu_adr_i[OPTION_ICACHE_BLOCK_WIDTH-1:0];
	 mem_adr <= cpu_adr_i;
	 /*
	  * First req in refill will always be a match,
	  * since that req was the one causing the refill
	  */
	 refill_match <= 1;
      end else if (state == REFILL) begin
	 if (ic_ack_i) begin
	    mem_adr <= next_mem_adr;
	    refill_match <= 0;
	    if (cpu_req_i) begin
	       if (cpu_adr_i == next_mem_adr)
		 refill_match <= 1;
	    end
	 end else if (cpu_req_i) begin
	       if (cpu_adr_i == mem_adr)
		 refill_match <= 1;
	 end
      end
   end

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       cpu_req_r <= 0;
     else
       cpu_req_r <= cpu_req_i;

   always @(*) begin
      next_state = state;
      cpu_ack = 1'b0;
      mem_req = 1'b0;
      tag_we = 1'b0;
      way_we = {(OPTION_ICACHE_WAYS){1'b0}};
      tag_din = tag_dout;

      case (state)
	IDLE: begin
	   if (cpu_req_i & cache_req & ic_enable)
	     next_state = READ;
	end

	READ: begin
	   if (invalidating) begin
	      next_state = IDLE;
	   end else if (hit) begin
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
	      next_state = IDLE;
	   end else begin
	      next_state = REFILL;
	   end
	end

	REFILL: begin
	   mem_req = 1'b1;
	   if (invalidating) begin
	      next_state = IDLE;
	   end else if (ic_ack_i) begin
	      if (OPTION_ICACHE_WAYS == 2) begin
		 if (lru)
		   way_we[1] = 1'b1;
		 else
		   way_we[0] = 1'b1;
	      end else begin
		   way_we[0] = 1'b1;
	      end
	      if (refill_match & ic_enable)
		 cpu_ack = 1'b1;

	      if (refill_done) begin
		 if (OPTION_ICACHE_WAYS == 2) begin
		    if (lru) begin // way 1
		       tag_din[TAG_WAY_VALID*2] = 1'b1;
		       tag_din[TAG_LRU] = 1'b0;
		       tag_din[(2*TAG_WAY_WIDTH)-2:TAG_WAY_WIDTH] = tag_index;
		    end else begin // way0
		       tag_din[TAG_WAY_VALID] = 1'b1;
		       tag_din[TAG_LRU] = 1'b1;
		       tag_din[TAG_WAY_WIDTH-2:0] = tag_index;
		    end
		 end else begin
		       tag_din[TAG_WAY_VALID] = 1'b1;
		       tag_din[TAG_LRU] = 1'b1;
		       tag_din[TAG_WAY_WIDTH-2:0] = tag_index;
		 end

		 tag_we = 1'b1;
		 next_state = IDLE;
	      end
	   end
	end
      endcase

      // Lazy invalidation, invalidate everything that matches tag address
      if (invalidating) begin
	 tag_din = 0;
	 tag_we = 1'b1;
      end

      if (ic_err_i)
	next_state = IDLE;
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
