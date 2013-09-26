/******************************************************************************
 This Source Code Form is subject to the terms of the
 Open Hardware Description License, v. 1.0. If a copy
 of the OHDL was not distributed with this file, You
 can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

 Description: Data cache implementation

 Copyright (C) 2012 Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>

 ******************************************************************************/

`include "mor1kx-defines.v"

module mor1kx_dcache
  #(
    parameter OPTION_OPERAND_WIDTH = 32,
    parameter OPTION_DCACHE_BLOCK_WIDTH = 5,
    parameter OPTION_DCACHE_SET_WIDTH = 9,
    parameter OPTION_DCACHE_WAYS = 2,
    parameter OPTION_DCACHE_LIMIT_WIDTH = 32
    )
   (
    input 			      clk,
    input 			      rst,

    input 			      dc_enable_i,
    input 			      dc_access_i,
    output 			      refill_o,
    output 			      refill_done_o,

    // CPU Interface
    output 			      cpu_err_o,
    output 			      cpu_ack_o,
    output [31:0] 		      cpu_dat_o,
    input [31:0] 		      cpu_dat_i,
    input [OPTION_OPERAND_WIDTH-1:0]  cpu_adr_i,
    input [OPTION_OPERAND_WIDTH-1:0]  cpu_adr_match_i,
    input 			      cpu_req_i,
    input 			      cpu_we_i,
    input [3:0] 		      cpu_bsel_i,

    input 			      refill_allowed,

    // BUS Interface
    input 			      dbus_err_i,
    input 			      dbus_ack_i,
    input [31:0] 		      dbus_dat_i,
    output [31:0] 		      dbus_dat_o,
    output [31:0] 		      dbus_adr_o,
    output 			      dbus_req_o,
    output [3:0] 		      dbus_bsel_o,

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
   localparam READ		= 5'b00010;
   localparam WRITE		= 5'b00100;
   localparam REFILL		= 5'b01000;
   localparam INVALIDATE	= 5'b10000;

   // Address space in bytes for a way
   localparam WAY_WIDTH = OPTION_DCACHE_BLOCK_WIDTH + OPTION_DCACHE_SET_WIDTH;
   /*
    * Tag layout
    * +-------------------------------------------------------------+
    * | LRU | wayN valid | wayN index |...| way0 valid | way0 index |
    * +-------------------------------------------------------------+
    */
   localparam TAG_INDEX_WIDTH = (OPTION_DCACHE_LIMIT_WIDTH - WAY_WIDTH);
   localparam TAG_WAY_WIDTH = TAG_INDEX_WIDTH + 1;
   localparam TAG_WAY_VALID = TAG_WAY_WIDTH;
   localparam TAG_WIDTH = TAG_WAY_WIDTH * OPTION_DCACHE_WAYS + 1;
   localparam TAG_LRU = TAG_WIDTH - 1;

   // FSM state signals
   reg [4:0] 			      state;
   wire				      idle;
   wire				      read;
   wire				      write;
   wire				      refill;

   reg [31:0] 			      dbus_adr;
   wire [31:0] 			      next_dbus_adr;
   reg [31:0] 			      way_wr_dat;
   wire 			      refill_done;
   wire 			      refill_hit;
   reg [(1<<(OPTION_DCACHE_BLOCK_WIDTH-2))-1:0] refill_valid;
   reg [(1<<(OPTION_DCACHE_BLOCK_WIDTH-2))-1:0] refill_valid_r;
   wire				      invalidate;

   wire [OPTION_DCACHE_SET_WIDTH-1:0] tag_raddr;
   wire [OPTION_DCACHE_SET_WIDTH-1:0] tag_waddr;
   reg [TAG_WIDTH-1:0]		      tag_din;
   reg 				      tag_we;
   wire [TAG_INDEX_WIDTH-1:0] 	      tag_index;
   wire [TAG_INDEX_WIDTH-1:0] 	      tag_windex;
   wire [TAG_WIDTH-1:0] 	      tag_dout;
   reg [TAG_WAY_WIDTH-1:0] 	      tag_save_data;
   reg 				      tag_save_lru;

   wire [WAY_WIDTH-3:0] 	      way_raddr[OPTION_DCACHE_WAYS-1:0];
   wire [WAY_WIDTH-3:0] 	      way_waddr[OPTION_DCACHE_WAYS-1:0];
   wire [OPTION_OPERAND_WIDTH-1:0]    way_din[OPTION_DCACHE_WAYS-1:0];
   wire [OPTION_OPERAND_WIDTH-1:0]    way_dout[OPTION_DCACHE_WAYS-1:0];
   reg [OPTION_DCACHE_WAYS-1:0]       way_we;

   wire 			      hit;
   wire [OPTION_DCACHE_WAYS-1:0]      way_hit;
   wire 			      lru;

   reg 				      write_pending;

   genvar 			      i;

   assign cpu_err_o = dbus_err_i;
   assign cpu_ack_o = ((read | refill) & hit & !write_pending |
		       refill_hit) & cpu_req_i;
   assign dbus_adr_o = dbus_adr;
   assign dbus_req_o = refill;
   assign dbus_dat_o = cpu_dat_i;
   assign dbus_bsel_o = 4'b1111;

   assign tag_raddr = cpu_adr_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH];
   /*
    * The tag mem is written during reads and writes to write the lru info and
    * during refill and invalidate.
    */
   assign tag_waddr = read | write ?
		      cpu_adr_match_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH] :
		      dbus_adr[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH];

   assign tag_index = cpu_adr_match_i[OPTION_DCACHE_LIMIT_WIDTH-1:WAY_WIDTH];
   assign tag_windex = dbus_adr[OPTION_DCACHE_LIMIT_WIDTH-1:WAY_WIDTH];

   generate
      if (OPTION_DCACHE_WAYS > 2) begin
	 initial begin
	    $display("ERROR: OPTION_DCACHE_WAYS > 2, not supported");
	    $finish();
	 end
      end

      for (i = 0; i < OPTION_DCACHE_WAYS; i=i+1) begin : ways
	 assign way_raddr[i] = cpu_adr_i[WAY_WIDTH-1:2];
	 assign way_waddr[i] = write ? cpu_adr_match_i[WAY_WIDTH-1:2] :
			       dbus_adr[WAY_WIDTH-1:2];
	 assign way_din[i] = way_wr_dat;
	 /*
	  * compare tag stored index with incoming index
	  * and check valid bit
	  */
	 assign way_hit[i] = tag_dout[((i + 1)*TAG_WAY_VALID)-1] &
			      (tag_dout[((i + 1)*TAG_WAY_WIDTH)-2:
					i*TAG_WAY_WIDTH] == tag_index);
      end
   endgenerate

   assign hit = |way_hit;

   generate
      if (OPTION_DCACHE_WAYS == 2) begin
	 assign cpu_dat_o = way_hit[0] | refill_hit & !tag_save_lru ?
			    way_dout[0] : way_dout[1];
      end else begin
	 assign cpu_dat_o = way_dout[0];
      end
   endgenerate

   assign lru = tag_dout[TAG_LRU];

   assign next_dbus_adr = (OPTION_DCACHE_BLOCK_WIDTH == 5) ?
			  {dbus_adr[31:5], dbus_adr[4:0] + 5'd4} : // 32 byte
			  {dbus_adr[31:4], dbus_adr[3:0] + 4'd4};  // 16 byte

   assign refill_done_o = refill_done;
   assign refill_done = refill_valid[next_dbus_adr[OPTION_DCACHE_BLOCK_WIDTH-1:2]];
   assign refill_hit = refill_valid_r[cpu_adr_match_i[OPTION_DCACHE_BLOCK_WIDTH-1:2]] &
		       cpu_adr_match_i[OPTION_DCACHE_LIMIT_WIDTH-1:
				       OPTION_DCACHE_BLOCK_WIDTH] ==
		       dbus_adr[OPTION_DCACHE_LIMIT_WIDTH-1:
				OPTION_DCACHE_BLOCK_WIDTH] &
		       refill & !write_pending;

   assign idle = (state == IDLE);
   assign refill = (state == REFILL);
   assign read = (state == READ);
   assign write = (state == WRITE);

   assign refill_o = refill;

   /*
    * SPR bus interface
    */

   // The SPR interface is used to invalidate the cache blocks. When
   // an invalidation is started, the respective entry in the tag
   // memory is cleared. When another transfer is in progress, the
   // handling is delayed until it is possible to serve it.
   //
   // The invalidation is acknowledged to the SPR bus, but the cycle
   // is terminated by the core. We therefore need to hold the
   // invalidate acknowledgement. Meanwhile we continuously write the
   // tag memory which is no problem.

   // Net that signals an acknowledgement
   reg invalidate_ack;

   // An invalidate request is either a block flush or a block invalidate
   assign invalidate = spr_bus_stb_i & spr_bus_we_i &
		       (spr_bus_addr_i == `OR1K_SPR_DCBFR_ADDR |
			spr_bus_addr_i == `OR1K_SPR_DCBIR_ADDR);

   // Acknowledge to the SPR bus.
   assign spr_bus_ack_o = invalidate_ack;

   /*
    * Cache FSM
    * Starts in IDLE.
    * State changes between READ and WRITE happens cpu_we_i is asserted or not.
    * cpu_we_i is in sync with cpu_adr_i, so that means that it's the
    * *upcoming* write that it is indicating. It only toggles for one cycle,
    * so if we are busy doing something else when this signal comes
    * (i.e. refilling) we assert the write_pending signal.
    * cpu_req_i is in sync with cpu_adr_match_i, so it can be used to
    * determined if a cache hit should cause a refill or if a write should
    * really be executed.
    */
   always @(posedge clk `OR_ASYNC_RST) begin
      if (rst | dbus_err_i) begin
	 state <= IDLE;
	 write_pending <= 0;
      end else begin
	 if (cpu_we_i)
	   write_pending <= 1;
	 else if (!cpu_req_i)
	   write_pending <= 0;

	 refill_valid_r <= refill_valid;

	 case (state)
	   IDLE: begin
	      if (invalidate) begin
		 // If there is an invalidation request
		 //
		 // Store address in dbus_adr that is muxed to the tag
		 // memory write address
		 dbus_adr <= spr_bus_dat_i;

		 // Change to invalidate state that actually accesses
		 // the tag memory
		 state <= INVALIDATE;
	      end else if (cpu_we_i | write_pending)
		state <= WRITE;
	      else if (cpu_req_i)
		state <= READ;
	   end

	   READ: begin
	      if (dc_access_i | cpu_we_i & dc_enable_i) begin
		 if (!hit & cpu_req_i & !write_pending & refill_allowed) begin
		    refill_valid <= 0;
		    refill_valid_r <= 0;
		    dbus_adr <= cpu_adr_match_i;
		    tag_save_lru <= lru;
		    if (OPTION_DCACHE_WAYS == 2) begin
		       if (lru)
			 tag_save_data <= tag_din[TAG_WAY_WIDTH-1:0];
		       else
			 tag_save_data <= tag_din[2*TAG_WAY_WIDTH-1:TAG_WAY_WIDTH];
		    end
		    state <= REFILL;
		 end else if (cpu_we_i | write_pending) begin
		    state <= WRITE;
		 end
	      end else if (!dc_enable_i) begin
		 state <= IDLE;
	      end
	   end
	   REFILL: begin
	      if (dbus_ack_i) begin
		 dbus_adr <= next_dbus_adr;
		 refill_valid[dbus_adr[OPTION_DCACHE_BLOCK_WIDTH-1:2]] <= 1;

		 if (refill_done)
		   state <= IDLE;
	      end
	   end

	   WRITE: begin
	      if (!dc_access_i | !cpu_req_i | !cpu_we_i) begin
		 write_pending <= 0;
		 state <= READ;
	      end
	   end

	   INVALIDATE: begin
	      if (invalidate) begin
		 // Store address in dbus_adr that is muxed to the tag
		 // memory write address
		 dbus_adr <= spr_bus_dat_i;

		 state <= INVALIDATE;
	      end else begin
		 state <= IDLE;
	      end
	   end

	   default:
	     state <= IDLE;
	 endcase // case (state)
      end // else: !if(rst | dbus_err_i)
   end // always @ (posedge clk `OR_ASYNC_RST)

   // This is the combinational part of the state machine that
   // interfaces the tag and way memories.

   always @(*) begin
      tag_we = 1'b0;
      tag_din = tag_dout;
      way_we = {(OPTION_DCACHE_WAYS){1'b0}};
      way_wr_dat = dbus_dat_i;

      // The default is (of course) not to acknowledge the invalidate
      invalidate_ack = 1'b0;

      case (state)
	IDLE: begin
	   // When idle we can always acknowledge the invalidate as it
	   // has the highest priority in handling. When something is
	   // changed on the state machine handling above this needs
	   // to be changed.
	   invalidate_ack = 1'b1;
	end
	READ: begin
	   if (hit) begin
	      /* output data and write back tag with LRU info */
	      if (way_hit[0]) begin
		 tag_din[TAG_LRU] = 1'b1;
	      end
	      if (OPTION_DCACHE_WAYS == 2) begin
		 if (way_hit[1]) begin
		    tag_din[TAG_LRU] = 1'b0;
		 end
	      end
	      tag_we = 1'b1;
	   end
	end

	WRITE: begin
	   way_wr_dat = cpu_dat_i;
	   if (hit & cpu_req_i) begin
	      /* Mux cache output with write data */
	      if (!cpu_bsel_i[3])
		way_wr_dat[31:24] = cpu_dat_o[31:24];
	      if (!cpu_bsel_i[2])
		way_wr_dat[23:16] = cpu_dat_o[23:16];
	      if (!cpu_bsel_i[1])
		way_wr_dat[15:8] = cpu_dat_o[15:8];
	      if (!cpu_bsel_i[0])
		way_wr_dat[7:0] = cpu_dat_o[7:0];

	      if (way_hit[0]) begin
		 way_we[0] = 1'b1;
		 tag_din[TAG_LRU] = 1'b1;
	      end
	      if (OPTION_DCACHE_WAYS == 2) begin
		 if (way_hit[1]) begin
		    way_we[1] = 1'b1;
		    tag_din[TAG_LRU] = 1'b0;
		 end
	      end
	      tag_we = 1'b1;
	   end
	end

	REFILL: begin
	   if (dbus_ack_i) begin
	      if (OPTION_DCACHE_WAYS == 2) begin
		 if (tag_save_lru)
		   way_we[1] = 1'b1;
		 else
		   way_we[0] = 1'b1;
	      end else begin
		 way_we[0] = 1'b1;
	      end

	      /* Invalidate the way on the first write */
	      if (refill_valid == 0) begin
		 if (tag_save_lru && OPTION_DCACHE_WAYS == 2)
		   tag_din[(2*TAG_WAY_VALID)-1] = 1'b0;
		 else
		   tag_din[TAG_WAY_VALID-1] = 1'b0;

		 tag_we = 1'b1;
	      end

	      if (refill_done) begin
		 if (OPTION_DCACHE_WAYS == 2) begin
		    if (tag_save_lru) begin // way 1
		       tag_din[(2*TAG_WAY_VALID)-1] = 1'b1;
		       tag_din[TAG_LRU] = 1'b0;
		       tag_din[(2*TAG_WAY_WIDTH)-2:TAG_WAY_WIDTH] = tag_windex;
		       tag_din[TAG_WAY_WIDTH-1:0] = tag_save_data;
		    end else begin // way0
		       tag_din[TAG_WAY_VALID-1] = 1'b1;
		       tag_din[TAG_LRU] = 1'b1;
		       tag_din[TAG_WAY_WIDTH-2:0] = tag_windex;
		       tag_din[2*TAG_WAY_WIDTH-1:TAG_WAY_WIDTH] = tag_save_data;
		    end
		 end else begin
		    tag_din[TAG_WAY_VALID-1] = 1'b1;
		    tag_din[TAG_LRU] = 1'b0;
		    tag_din[TAG_WAY_WIDTH-2:0] = tag_windex;
		 end

		 tag_we = 1'b1;
	      end
	   end
	end

	INVALIDATE: begin
	   invalidate_ack = 1'b1;

	   // Lazy invalidation, invalidate everything that matches
	   // tag address
	   tag_din = 0;
	   tag_we = 1'b1;
	end

	default: begin
	end
      endcase
   end

   generate
      for (i = 0; i < OPTION_DCACHE_WAYS; i=i+1) begin : way_memories
	 mor1kx_simple_dpram_sclk
	       #(
		 .ADDR_WIDTH(WAY_WIDTH-2),
		 .DATA_WIDTH(OPTION_OPERAND_WIDTH),
		 .ENABLE_BYPASS("TRUE")
		 )
	 way_data_ram
	       (
		// Outputs
		.dout			(way_dout[i]),
		// Inputs
		.clk			(clk),
		.raddr			(way_raddr[i][WAY_WIDTH-3:0]),
		.waddr			(way_waddr[i][WAY_WIDTH-3:0]),
		.we			(way_we[i]),
		.din			(way_din[i][31:0]));

      end
   endgenerate

   mor1kx_simple_dpram_sclk
     #(
       .ADDR_WIDTH(OPTION_DCACHE_SET_WIDTH),
       .DATA_WIDTH(TAG_WIDTH),
       .ENABLE_BYPASS("TRUE")
     )
   tag_ram
     (
      // Outputs
      .dout				(tag_dout[TAG_WIDTH-1:0]),
      // Inputs
      .clk				(clk),
      .raddr				(tag_raddr),
      .waddr				(tag_waddr),
      .we				(tag_we),
      .din				(tag_din));

endmodule
