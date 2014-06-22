/******************************************************************************
 This Source Code Form is subject to the terms of the
 Open Hardware Description License, v. 1.0. If a copy
 of the OHDL was not distributed with this file, You
 can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

 Description: Data cache implementation

 Copyright (C) 2012-2013
    Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>
    Stefan Wallentowitz <stefan.wallentowitz@tum.de>

 ******************************************************************************/

`include "mor1kx-defines.v"

// This is the actual data cache with the following properties:
//  - Configurable number of ways
//  - Configurable block size
//  - Snooping, configurable with extra tag memory
//  - Write misses do not lead to refills
//  - Virtually index, physically tagged
//  - Only LRU (least recently used) replacement policy
//
// = Internals =
//
// For a better understanding of the internals it is useful to split
// the functionality in different aspects: cache organization, tag
// handling, way access and the state machine.
//
// == Organization ==
//
// The cache has essentially two memories: the tag memory and the
// actual data memory. Both contain contains 2^OPTION_DCACHE_SET_WIDTH
// entries (adressed via the index). If OPTION_DCACHE_SNOOP_TAGMEM is
// set to ENABLED, the tag memory is duplicated. The snoop checking
// uses then this memory and writes are done to both memories.
//
// Each tag memory entry is organized as:
//
//  +---------------------------------------------------------+
//  | LRU | wayN valid | wayN tag |...| way0 valid | way0 tag |
//  +---------------------------------------------------------+
//
// == Interfaces ==
//
// The LSU drives the cache input directly from the pipeline. The
// interface of the cpu_* signals is straight forward. cpu_req_i is
// driven by the pipeline control once the pipeline starts waiting for
// the LSU to finish. A write is preceeded with the cpu_we_i signal
// which is only active for one cycle.
//
// == Tag handling ==
//
// The tags are continuously read and the index (tagmem_rindex) to
// read is principally the index extracted from cpu_adr_i (see begin
// of process 'comb_tagandway'). In case of a snoop and if the snoop
// is not configured with a separate tag memory, the snoop can always
// obstruct the reading, which is signaled to the LSU via the
// snoop_read_tagmem_o signal.
//
// Depending on the hit or miss information, the tag is then written
// in the next cycle (or after refill on a read miss).
//
// == Snooping ==
//
// Snoop is not an extra state as it overlays the normal operation
// (lets for the moment assume it can happen at any point in time).
// Instead it only overlays both operations. When a snoop event occurs
// and there is no extra snoop tag memory, there are no state
// transitions as we cannot check for a hit or miss in the next cycle.
// This is signaled to the LSU via the snoop_read_tagmem_o signal as
// the LSU actually controls the whole operation.
//
// In the next cycle after the snoop event, we then check whether the
// snooped address matched one of the ways. If so, it will then stall
// the write operations to the tag memory. This is also visible to the
// LSU via the snoop_hit_o signal.
//
// == State machine ==
//
// There is a state machine that determines the current state once the
// hit or miss information is available.

module mor1kx_dcache
  #(
    parameter OPTION_OPERAND_WIDTH = 32,
    parameter OPTION_DCACHE_BLOCK_WIDTH = 5,
    parameter OPTION_DCACHE_SET_WIDTH = 9,
    parameter OPTION_DCACHE_WAYS = 2,
    parameter OPTION_DCACHE_LIMIT_WIDTH = 32,
    parameter OPTION_DCACHE_SNOOP_TAGMEM = "ENABLED"
    )
   (
    input 			      clk,
    input 			      rst,

    input 			      dc_enable_i,
    input 			      dc_access_i,
    output 			      refill_o,
    output 			      refill_done_o,

    // CPU Interface
    // Generate an error
    output 			      cpu_err_o,
    // Acknowledge access
    output 			      cpu_ack_o,
    // Data output (on read)
    output reg [31:0] 		      cpu_dat_o,
    // Data input (on write)
    input [31:0] 		      cpu_dat_i,
    // Address to access
    input [OPTION_OPERAND_WIDTH-1:0]  cpu_adr_i,
    // Translated address (one cycle delayed)
    input [OPTION_OPERAND_WIDTH-1:0]  cpu_adr_match_i,
    // Trigger a request
    input 			      cpu_req_i,
    // Write request, goes up one cycle before req
    input 			      cpu_we_i,
    // Select for write
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
    output 			      spr_bus_ack_o,

    input [31:0] 		      snoop_adr_i,
    input 			      snoop_en_i,
    // The cache does not check the tag memory this cycle due to a
    // snoop read access. This can be avoided using a separate snoop
    // tag memory
    output 			      snoop_read_tagmem_o,
    // The snoop produced a hit and this cycle is reserved for the
    // snoop invalidation. Other write accesses are stalled
    output 			      snoop_hit_o,

    output 			      traceport_start_o,
    output 			      traceport_end_o,
    output 			      traceport_read_o,
    output 			      traceport_write_o,
    output 			      traceport_hit_o,
    output 			      traceport_miss_o,
    output 			      traceport_snoop_o
    );


   // States
   localparam READ		= 4'b0001;
   localparam WRITE		= 4'b0010;
   localparam REFILL		= 4'b0100;
   localparam INVALIDATE	= 4'b1000;

   // Address space in bytes for a way
   localparam WAY_WIDTH = OPTION_DCACHE_BLOCK_WIDTH + OPTION_DCACHE_SET_WIDTH;
   /*
    * Tag memory layout
    *            +---------------------------------------------------------+
    * (index) -> | LRU | wayN valid | wayN tag |...| way0 valid | way0 tag |
    *            +---------------------------------------------------------+
    */

   // The tag is the part left of the index
   localparam TAG_WIDTH = (OPTION_DCACHE_LIMIT_WIDTH - WAY_WIDTH);

   // The tag memory contains entries with OPTION_DCACHE_WAYS parts of
   // each TAGMEM_WAY_WIDTH. Each of those is tag and a valid flag.
   localparam TAGMEM_WAY_WIDTH = TAG_WIDTH + 1;
   localparam TAGMEM_WAY_VALID = TAGMEM_WAY_WIDTH - 1;

   // Additionally, the tag memory entry contains an LRU value. The
   // width of this is 0 for OPTION_DCACHE_LIMIT_WIDTH==1
   localparam TAG_LRU_WIDTH = OPTION_DCACHE_WAYS*(OPTION_DCACHE_WAYS-1) >> 1;

   // We have signals for the LRU which are not used for one way
   // caches. To avoid signal width [-1:0] this generates [0:0]
   // vectors for them, which are removed automatically then.
   localparam TAG_LRU_WIDTH_BITS = (OPTION_DCACHE_WAYS >= 2) ? TAG_LRU_WIDTH : 1;

   // Compute the total sum of the entry elements
   localparam TAGMEM_WIDTH = TAGMEM_WAY_WIDTH * OPTION_DCACHE_WAYS + TAG_LRU_WIDTH;

   // For convenience we define the position of the LRU in the tag
   // memory entries
   localparam TAG_LRU_MSB = TAGMEM_WIDTH - 1;
   localparam TAG_LRU_LSB = TAG_LRU_MSB - TAG_LRU_WIDTH + 1;

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

   // The index we read and write from tag memory
   reg [OPTION_DCACHE_SET_WIDTH-1:0]  tagmem_rindex;
   reg [OPTION_DCACHE_SET_WIDTH-1:0]  tagmem_windex;

   // The data from the tag memory
   wire [TAGMEM_WIDTH-1:0] 	      tagmem_dout;
   wire [TAG_LRU_WIDTH_BITS-1:0]      tag_lru_out;
   wire [TAGMEM_WAY_WIDTH-1:0] 	      tag_way_out [OPTION_DCACHE_WAYS-1:0];

   // The data to the tag memory
   wire [TAGMEM_WIDTH-1:0] 	      tagmem_din;
   reg [TAG_LRU_WIDTH_BITS-1:0]       tag_lru_in;
   reg [TAGMEM_WAY_WIDTH-1:0] 	      tag_way_in [OPTION_DCACHE_WAYS-1:0];

   reg [TAGMEM_WAY_WIDTH-1:0] 	      tag_way_save[OPTION_DCACHE_WAYS-1:0];

   // Whether to write to the tag memory in this cycle
   reg 				      tagmem_we;

   // This is the tag we need to write to the tag memory during refill
   wire [TAG_WIDTH-1:0] 	      cpu_wtag;

   // This is the tag we check against
   wire [TAG_WIDTH-1:0] 	      cpu_tag;

   // Access to the way memories
   wire [WAY_WIDTH-3:0] 	      way_raddr[OPTION_DCACHE_WAYS-1:0];
   wire [WAY_WIDTH-3:0] 	      way_waddr[OPTION_DCACHE_WAYS-1:0];
   wire [OPTION_OPERAND_WIDTH-1:0]    way_din[OPTION_DCACHE_WAYS-1:0];
   wire [OPTION_OPERAND_WIDTH-1:0]    way_dout[OPTION_DCACHE_WAYS-1:0];
   reg [OPTION_DCACHE_WAYS-1:0]       way_we;

   // Does any way hit?
   wire 			      tagmem_hit;
   wire 			      cpu_hit;
   wire [OPTION_DCACHE_WAYS-1:0]      way_hit;

   // This is the least recently used value before access the memory.
   // Those are one hot encoded.
   wire [OPTION_DCACHE_WAYS-1:0]      lru;

   // Register that stores the LRU value from lru
   reg [OPTION_DCACHE_WAYS-1:0]       tag_save_lru;

   // The access vector to update the LRU history is the way that has
   // a hit or is refilled. It is also one-hot encoded.
   reg [OPTION_DCACHE_WAYS-1:0]       access;

   // The current LRU history as read from tag memory and the update
   // value after we accessed it to write back to tag memory.
   wire [TAG_LRU_WIDTH_BITS-1:0]      current_lru_history;
   wire [TAG_LRU_WIDTH_BITS-1:0]      next_lru_history;

   // Intermediate signals to ease debugging
   wire [TAG_WIDTH-1:0]               check_way_tag [OPTION_DCACHE_WAYS-1:0];
   wire                               check_way_match [OPTION_DCACHE_WAYS-1:0];
   wire                               check_way_valid [OPTION_DCACHE_WAYS-1:0];

   reg 				      write_pending;

   /*
    * Snooping
    */

   // This is the snoop read interface. When the extra snoop tag
   // memory is activated, the snoop_read_tagmem signal is used to
   // instantly read from the normal tag memory.

   // A write operation is observed, read tag memory
   wire 			      snoop_read;
   assign snoop_read = snoop_en_i;

   // This read needs to go to the tag memory
   wire 			      snoop_read_tagmem;
   assign snoop_read_tagmem = snoop_read & (OPTION_DCACHE_SNOOP_TAGMEM == "NONE");
   assign snoop_read_tagmem_o = snoop_read_tagmem;

   // Extract index to read from snooped address
   wire [OPTION_DCACHE_SET_WIDTH-1:0] snoop_index;
   assign snoop_index = snoop_adr_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH];

   wire [OPTION_DCACHE_SET_WIDTH-1:0] snoopmem_rindex;
   assign snoopmem_rindex = snoop_index;

   // To bring the snoop event to the next cycle, the snoop_check
   // register is used to compare the snoop_tag to the memories in the
   // next cycle

   // Register that is high one cycle after the actual snoop event to
   // drive the comparison
   reg 				      snoop_check;
   // Register that stores the tag for one cycle
   reg [TAG_WIDTH-1:0] 		      snoop_tag;
   // Also store the index for one cycle, for the succeeding write access
   reg [OPTION_DCACHE_SET_WIDTH-1:0]  snoop_windex;
   wire 			      snoop_check_tagmem;
   assign snoop_check_tagmem = snoop_check & (OPTION_DCACHE_SNOOP_TAGMEM == "NONE");

   // Snoop tag memory interface
   // Data out of tag memory
   wire [TAGMEM_WIDTH-1:0] 	      snoopmem_dout;
   // Each ways information in the tag memory
   wire [TAGMEM_WAY_WIDTH-1:0] 	      snoopmem_way_out [OPTION_DCACHE_WAYS-1:0];
   // Each ways tag in the tag memory
   wire [TAG_WIDTH-1:0] 	      snoopmem_check_way_tag [OPTION_DCACHE_WAYS-1:0];
   // Whether the tag matches the snoop tag
   wire                               snoopmem_check_way_match [OPTION_DCACHE_WAYS-1:0];
   // Whether the tag is valid
   wire                               snoopmem_check_way_valid [OPTION_DCACHE_WAYS-1:0];
   // Whether the way hits
   wire [OPTION_DCACHE_WAYS-1:0]      snoopmem_way_hit;
   // Whether any way hits
   wire 			      snoopmem_hit;

   // Snoop hit result which is multiplexed either the tag memory
   // check result if (OPTION_DCACHE_SNOOP_TAGMEM=="NONE") or the
   // check result from the snoop tag memory
   wire [OPTION_DCACHE_WAYS-1:0]      snoop_way_hit;
   wire 			      snoop_hit;

   assign snoop_hit_o = snoop_hit;

   genvar 			      i;

   assign cpu_err_o = dbus_err_i;
   assign cpu_ack_o = ((read | refill) & cpu_hit & !write_pending |
		       refill_hit) & cpu_req_i;
   assign dbus_adr_o = dbus_adr;
   assign dbus_req_o = refill;
   assign dbus_dat_o = cpu_dat_i;
   assign dbus_bsel_o = 4'b1111;

   // Tag checking
   generate
      if (OPTION_DCACHE_WAYS >= 2) begin
         // Multiplex the LRU history from and to tag memory
         assign current_lru_history = tagmem_dout[TAG_LRU_MSB:TAG_LRU_LSB];
         assign tagmem_din[TAG_LRU_MSB:TAG_LRU_LSB] = tag_lru_in;
         assign tag_lru_out = tagmem_dout[TAG_LRU_MSB:TAG_LRU_LSB];
      end

      for (i = 0; i < OPTION_DCACHE_WAYS; i=i+1) begin : ways
	 assign way_raddr[i] = cpu_adr_i[WAY_WIDTH-1:2];
	 assign way_waddr[i] = write ? cpu_adr_match_i[WAY_WIDTH-1:2] :
			       dbus_adr[WAY_WIDTH-1:2];
	 assign way_din[i] = way_wr_dat;

	 // De-multiplex the ways' tag memory storage
         assign tag_way_out[i] = tagmem_dout[(i+1)*TAGMEM_WAY_WIDTH-1:i*TAGMEM_WAY_WIDTH];

	 // Extract tags for all ways from tag memory
         assign check_way_tag[i] = tag_way_out[i][TAGMEM_WAY_WIDTH-1:0];

	 // Extract valid information for ways
         assign check_way_valid[i] = tag_way_out[i][TAGMEM_WAY_VALID];

	 // Match the tags. If a snoop operation is in progress and we
	 // do not have a separate snoop tag memory, this overlays
	 // tagmem_rindex was the snooped index in the cycle before,
	 // so that we have to compare to the stored snooping tag now.
         assign check_way_match[i] = (snoop_check & (OPTION_DCACHE_SNOOP_TAGMEM == "NONE")) ?
				     (check_way_tag[i] == snoop_tag) :
				     (check_way_tag[i] == cpu_tag);

	 // Does any way hit?
         assign way_hit[i] = check_way_valid[i] & check_way_match[i];

	 if (OPTION_DCACHE_SNOOP_TAGMEM != "NONE") begin
	    // The same for the snoop tag memory
            assign snoopmem_way_out[i] = snoopmem_dout[(i+1)*TAGMEM_WAY_WIDTH-1:i*TAGMEM_WAY_WIDTH];

	     assign snoopmem_check_way_tag[i] = snoopmem_way_out[i][TAGMEM_WAY_WIDTH-1:0];
            assign snoopmem_check_way_match[i] = (snoopmem_check_way_tag[i] == snoop_tag);
            assign snoopmem_check_way_valid[i] = snoopmem_way_out[i][TAGMEM_WAY_VALID];

            assign snoopmem_way_hit[i] = snoopmem_check_way_valid[i] & snoopmem_check_way_match[i];
	 end

         // Multiplex the way entries in the tag memory
         assign tagmem_din[(i+1)*TAGMEM_WAY_WIDTH-1:i*TAGMEM_WAY_WIDTH] = tag_way_in[i];
      end
   endgenerate

   // Did any way hit (or snoop hit)
   assign tagmem_hit = |way_hit;
   // Did any way hit in the snoop tag memory
   assign snoopmem_hit = |snoopmem_way_hit;

   // This one is only high for a hit that was caused by a cpu
   // operation
   assign cpu_hit = tagmem_hit &
		     ((OPTION_DCACHE_SNOOP_TAGMEM != "NONE") |
		      !snoop_check_tagmem);

   // Multiplex snoop tag memory hits or normal tag memory hits, also
   // mask with snoop_check
   assign snoop_hit = snoop_check &
		      ((OPTION_DCACHE_SNOOP_TAGMEM == "NONE") ?
		       tagmem_hit : snoopmem_hit);

   // Also multiplex the way for the actual invalidation
   assign snoop_way_hit = (OPTION_DCACHE_SNOOP_TAGMEM == "NONE") ?
			  way_hit : snoopmem_way_hit;

   integer w0;
   always @(*) begin
      cpu_dat_o = {OPTION_OPERAND_WIDTH{1'bx}};

      // Put correct way on the data port
      for (w0 = 0; w0 < OPTION_DCACHE_WAYS; w0 = w0 + 1) begin
         if (way_hit[w0] | (refill_hit & tag_save_lru[w0])) begin
            cpu_dat_o = way_dout[w0];
         end
      end
   end

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

   assign refill = (state == REFILL);
   assign read = (state == READ);
   assign write = (state == WRITE);

   assign refill_o = refill;

   /* * SPR bus interface */

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
    * State changes between READ and WRITE happens cpu_we_i is asserted or not.
    * cpu_we_i is in sync with cpu_adr_i, so that means that it's the
    * *upcoming* write that it is indicating. It only toggles for one cycle,
    * so if we are busy doing something else when this signal comes
    * (i.e. refilling) we assert the write_pending signal.
    * cpu_req_i is in sync with cpu_adr_match_i, so it can be used to
    * determined if a cache hit should cause a refill or if a write should
    * really be executed.
    */
   integer w1;
   always @(posedge clk `OR_ASYNC_RST) begin
      if (rst | dbus_err_i) begin
	 state <= READ;
	 write_pending <= 0;
      end else begin
	 if (cpu_we_i)
	   write_pending <= 1;
	 else if (!cpu_req_i)
	   write_pending <= 0;

	 refill_valid_r <= refill_valid;

	 if (snoop_read) begin
	    // If there is a snoop event, we need to store this
	    // information. This happens independent of whether we
	    // have a snoop tag memory or not.
	    snoop_check <= 1;
	    snoop_windex <= snoopmem_rindex;
	    snoop_tag <= snoop_adr_i[OPTION_DCACHE_LIMIT_WIDTH-1:WAY_WIDTH];
	 end else begin
	    snoop_check <= 0;
	 end

	 // We can only handle external requests when no snoop
	 // checking is needed which is either no snoop event or we
	 // have the separate tag memory for snoop checking
	 case (state)
	   READ: begin
	      if (dc_access_i | cpu_we_i & dc_enable_i) begin
		 if (!cpu_hit & !snoop_check_tagmem & cpu_req_i &
		     !write_pending & refill_allowed) begin
		    refill_valid <= 0;
		    refill_valid_r <= 0;
		    dbus_adr <= cpu_adr_match_i;

		    // Store the LRU information for correct replacement
                    // on refill. Always one when only one way.
                    tag_save_lru <= (OPTION_DCACHE_WAYS==1) | lru;

		    for (w1 = 0; w1 < OPTION_DCACHE_WAYS; w1 = w1 + 1) begin
		       tag_way_save[w1] <= tag_way_out[w1];
		    end

		    state <= REFILL;
		 end else if (cpu_we_i | write_pending) begin
		    state <= WRITE;
		 end else if (invalidate) begin
		    state <= INVALIDATE;
		 end
	      end else if (invalidate) begin
		 state <= INVALIDATE;
	      end
	   end
	   REFILL: begin
	      if (dbus_ack_i) begin
		 dbus_adr <= next_dbus_adr;
		 refill_valid[dbus_adr[OPTION_DCACHE_BLOCK_WIDTH-1:2]] <= 1;

		 if (refill_done)
		   state <= READ;
	      end
	   end

	   WRITE: begin
	      if ((!dc_access_i | !cpu_req_i | !cpu_we_i) & !snoop_hit) begin
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
		 state <= READ;
	      end
	   end

	   default:
	     state <= READ;
	 endcase // case (state)
      end // else: !if(rst | dbus_err_i)
   end // always @ (posedge clk `OR_ASYNC_RST)

   // Tag and way handling
   assign cpu_tag = cpu_adr_match_i[OPTION_DCACHE_LIMIT_WIDTH-1:WAY_WIDTH];
   assign cpu_wtag = dbus_adr[OPTION_DCACHE_LIMIT_WIDTH-1:WAY_WIDTH];

   integer w2;

   always @(*) begin : comb_tagandway
      /* Read tag */
      // Permantly read from the tag index tagmem_rindex. If there is no
      // snoop obstructing this, this is the index from the cpu.
      if (snoop_read_tagmem) begin
	 tagmem_rindex = snoop_index;
      end else begin
	 tagmem_rindex = cpu_adr_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH];
      end

      /* Write tag and way */
      // We define the default assignments to the SRAM input. The
      // default is to keep data, don't write and don't access
      // anything (input to the LRU)
      tag_lru_in = tag_lru_out;
      for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
         tag_way_in[w2] = tag_way_out[w2];
      end

      tagmem_we = 1'b0;
      way_we = {(OPTION_DCACHE_WAYS){1'b0}};

      access = {(OPTION_DCACHE_WAYS){1'b0}};

      // The default data to write to the way is the data from the bus
      // during refill (and only then way_we is also assigned). In
      // case of a write this value is changed to the data from the
      // bus.
      way_wr_dat = dbus_dat_i;

      // Default is not to write the ways
      way_we = 0;

      // The default is (of course) not to acknowledge the invalidate
      invalidate_ack = 1'b0;

      // If we have a snoop hit, the tag memory and potentially the
      // snoop tag memory need to be invalidated.
      if (snoop_hit) begin
	 // This is the write access
	 tagmem_we = 1'b1;
	 tagmem_windex = snoop_windex;
	 for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
	    if (snoop_way_hit[w2]) begin
	       tag_way_in[w2] = 0;
	    end else if (OPTION_DCACHE_SNOOP_TAGMEM != "NONE") begin
	       tag_way_in[w2] = snoopmem_way_out[w2];
	    end
	 end
      end else begin
	 // The snoop hit will obstruct any other write operation in
	 // this cycle.
	 tagmem_windex = dbus_adr[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH];
	 case (state)
	   READ: begin
	      // In the previous cycle the tag was addressed with the
	      // index of the request. If we have a hit, we need to
	      // update the LRU information, which we do below. The
	      // state transition is controlled above.
	      tagmem_windex = cpu_adr_match_i[WAY_WIDTH-1:
					      OPTION_DCACHE_BLOCK_WIDTH];
	      if (dc_access_i  & cpu_hit & dc_enable_i & cpu_req_i) begin
		 // We got a hit. The LRU module gets the access
		 // information. Depending on this we update the LRU
		 // history in the tag.
		 access = way_hit;

		 // This is the updated LRU history after hit
		 tag_lru_in = next_lru_history;

		 tagmem_we = 1'b1;
	      end
	   end
	   WRITE: begin
	      // In the previous cycle the tag was addressed with the
	      // index of the request.
	      tagmem_windex = cpu_adr_match_i[WAY_WIDTH-1:
					      OPTION_DCACHE_BLOCK_WIDTH];

	      way_wr_dat = cpu_dat_i;
	      if (cpu_hit & cpu_req_i) begin
		 /* Mux cache output with write data */
		 if (!cpu_bsel_i[3])
		   way_wr_dat[31:24] = cpu_dat_o[31:24];
		 if (!cpu_bsel_i[2])
		   way_wr_dat[23:16] = cpu_dat_o[23:16];
		 if (!cpu_bsel_i[1])
		   way_wr_dat[15:8] = cpu_dat_o[15:8];
		 if (!cpu_bsel_i[0])
		   way_wr_dat[7:0] = cpu_dat_o[7:0];

		 way_we = way_hit;

		 tag_lru_in = next_lru_history;

		 tagmem_we = 1'b1;
	      end
	   end

	   REFILL: begin
	      if (dbus_ack_i) begin
		 // Snoop hint: This cannot happen during snoop
		 // operations as they can only come from the bus.
		 // Write the data to the way that is replaced (which
		 // is the LRU)
		 way_we = tag_save_lru;

		 // Access pattern
		 access = tag_save_lru;

		 /* Invalidate the way on the first write */
		 if (refill_valid == 0) begin
		    for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
                       if (tag_save_lru[w2]) begin
			  tag_way_in[w2][TAGMEM_WAY_VALID] = 1'b0;
                       end
                    end

		    tagmem_we = 1'b1;
		 end

		 // After refill update the tag memory entry of the
		 // filled way with the LRU history, the tag and set
		 // valid to 1.
		 if (refill_done) begin
		    for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
		       tag_way_in[w2] = tag_way_save[w2];
                       if (tag_save_lru[w2]) begin
			  tag_way_in[w2] = { 1'b1, cpu_wtag };
                       end
                    end
                    tag_lru_in = next_lru_history;

		    tagmem_we = 1'b1;
		 end
	      end
	   end

	   INVALIDATE: begin
	      invalidate_ack = 1'b1;

	      // Lazy invalidation, invalidate everything that matches tag address
              tag_lru_in = 0;
              for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
		 tag_way_in[w2] = 0;
              end

	      tagmem_we = 1'b1;
	   end

	   default: begin
	   end
	 endcase
      end
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

      if (OPTION_DCACHE_WAYS >= 2) begin : gen_u_lru
         /* mor1kx_cache_lru AUTO_TEMPLATE(
          .current  (current_lru_history),
          .update   (next_lru_history),
          .lru_pre  (lru),
          .lru_post (),
          .access   (access),
          ); */

         mor1kx_cache_lru
           #(.NUMWAYS(OPTION_DCACHE_WAYS))
         u_lru(/*AUTOINST*/
	       // Outputs
	       .update			(next_lru_history),	 // Templated
	       .lru_pre			(lru),			 // Templated
	       .lru_post		(),			 // Templated
	       // Inputs
	       .current			(current_lru_history),	 // Templated
	       .access			(access));		 // Templated
      end // if (OPTION_DCACHE_WAYS >= 2)
   endgenerate

   mor1kx_simple_dpram_sclk
     #(
       .ADDR_WIDTH(OPTION_DCACHE_SET_WIDTH),
       .DATA_WIDTH(TAGMEM_WIDTH),
       .ENABLE_BYPASS("TRUE")
     )
   tag_ram
     (
      // Outputs
      .dout				(tagmem_dout[TAGMEM_WIDTH-1:0]),
      // Inputs
      .clk				(clk),
      .raddr				(tagmem_rindex),
      .waddr				(tagmem_windex),
      .we				(tagmem_we),
      .din				(tagmem_din));

generate
if (OPTION_DCACHE_SNOOP_TAGMEM != "NONE") begin
   mor1kx_simple_dpram_sclk
     #(
       .ADDR_WIDTH(OPTION_DCACHE_SET_WIDTH),
       .DATA_WIDTH(TAGMEM_WIDTH),
       .ENABLE_BYPASS("TRUE")
       )
   snoop_tag_ram
     (
      // Outputs
      .dout			(snoopmem_dout[TAGMEM_WIDTH-1:0]),
      // Inputs
      .clk			(clk),
      .raddr			(snoopmem_rindex),
      .waddr			(tagmem_windex),
      .we			        (tagmem_we),
      .din			(tagmem_din));
end
endgenerate
endmodule
