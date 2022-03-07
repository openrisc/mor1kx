/* ****************************************************************************
  SPDX-License-Identifier: CERN-OHL-W-2.0

  Description: Data cache implementation

  Copyright (C) 2012-2013
     Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>
     Stefan Wallentowitz <stefan.wallentowitz@tum.de>

 ******************************************************************************/

// The mor1kx dcache is implemented as a write around cache with an
// optimization to populate cache line (write though) entries if a there is
// a valid entry in the dcache.

// Cases:

// 1. Write to cached memory entry
//    A data cache write operation will update cached way data if there is
//    a valid cache-line entry.  A write request must be guaranteed to finish in
//    2 clock cycles.  First clock cycle request, second clock cycle write.  The
//    LSU does not expect a response and will only present the write request to
//    the data cache for 2 clock cycles.  This will be extended only if there is
//    a snoop hit.
//
//    A write starts by transitioning the data cache FSM into WRITE state.
//    While in the WRITE state the tag memory and way memory will be written to.
//
//    If already in WRITE state a write option can complete in one cycle.
//
// 2. Write to non-cached memory entry
//    A data cache write to a non-cached entry is similar to a cached write
//    however tag and way memory will not be updated.  The FSM will sill need to
//    transition to the WRITE state in order to check the cache-line.
//
// 3. Read from cached memory entry
//    A data cache read will first transition the data cache FSM to the READ
//    state.  When in the read state a valid entry in the way memory will be
//    represented as a hit.
//
//    The cache-line data be provided back to the LSU.  This is done by
//    asserting the cpu ack line.
//
//    If the data cache is already in the READ state valid read requests will
//    complete in 1 clock cycle.
//
// 4. Read from non-cached memory entry
//    A data cache read for a non-cached memory entry will first transition the
//    FSM to the READ state to check the cache-line.  If the cache-line does not
//    have a valid entry (miss) the data cache will transition to the REFILL
//    state.  During REFILL the data cache requests the LSU to operate the data
//    bus and provide cache REFILL data.  When a cache-line if filled the data
//    cache requests the LSU to stop.
//
//    During refill when the request cache-line entry is being filled it will be
//    provided back to the LSU.  This provides better performance as the pending
//    read does not need to wait for the refill to complete.  This is done by
//    asserting the cpu ack line.
//
// 5. SPR request to invalidate or flush entries
//    An data cache SPR request will first transition the FSM into the
//    INVALIDATE state.  Once in the invalidate state the requested cache-line
//    entries will be invalidated.  The completion of this operation is
//    represented as an SPR ack.
//
// 6. Snoop Operation
//    Snoop is a signal that comes when there has been a CPU external memory
//    write on bus.  The data cache must invalidate valid entries in tag
//    memory when this occurs.
//
//    Snoop operations are highest priority and like other operations take
//    a maximum of 2 clock cycles.  One cycle to register the request and one
//    cycle to perform the invalidation.
//
//    When there is a snoop hit the data cache indicates this to the LSU to
//    delay any pending writes.

`include "mor1kx-defines.v"

module mor1kx_dcache
  #(
    parameter OPTION_OPERAND_WIDTH = 32,
    parameter OPTION_DCACHE_BLOCK_WIDTH = 5,
    parameter OPTION_DCACHE_SET_WIDTH = 9,
    parameter OPTION_DCACHE_WAYS = 2,
    parameter OPTION_DCACHE_LIMIT_WIDTH = 32,
    parameter OPTION_DCACHE_SNOOP = "NONE"
    )
   (
    input 			      clk,
    input 			      rst,

    input 			      dc_dbus_err_i,
    // Indicates if data cache is enabled on the CPU
    input 			      dc_enable_i,
    // Indicates the data cache is being accessed for a read or write
    input 			      dc_access_i,

    // Refill Interface
    // Indicate to LSU that refill is in progress
    output 			      refill_o,
    // Request to the LSU to start and complete a refill transaction
    // at the current read address.
    output 			      refill_req_o,
    output 			      refill_done_o,
    // Refill inputs from the LSU
    input 			      refill_allowed_i,
    input [OPTION_OPERAND_WIDTH-1:0]  refill_adr_i,
    input [OPTION_OPERAND_WIDTH-1:0]  refill_dat_i,
    input 			      refill_we_i,

    output 			      cache_hit_o,

    // CPU Interface
    output 			      cpu_err_o,
    output 			      cpu_ack_o,
    output reg [OPTION_OPERAND_WIDTH-1:0] cpu_dat_o,
    input [OPTION_OPERAND_WIDTH-1:0]  cpu_dat_i,
    input [OPTION_OPERAND_WIDTH-1:0]  cpu_adr_i,
    input [OPTION_OPERAND_WIDTH-1:0]  cpu_adr_match_i,
    input 			      cpu_req_i,
    input 			      cpu_we_i,
    input [3:0] 		      cpu_bsel_i,

    // Snoop address
    input [31:0] 		      snoop_adr_i,
    // Snoop event in this cycle
    input 			      snoop_valid_i,
    // Whether the snoop hit. If so, there will be no tag memory write
    // this cycle. The LSU may need to stall the pipeline.
    output 			      snoop_hit_o,

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
   wire				      read;
   wire				      write;
   wire				      refill;

   reg [WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH] invalidate_adr;
   wire [31:0] 			      next_refill_adr;
   reg [31:0] 			      way_wr_dat;
   wire 			      refill_done;
   wire 			      refill_hit;
   reg [(1<<(OPTION_DCACHE_BLOCK_WIDTH-2))-1:0] refill_valid;
   reg [(1<<(OPTION_DCACHE_BLOCK_WIDTH-2))-1:0] refill_valid_r;
   wire				      invalidate;

   // The index we read and write from tag memory
   wire [OPTION_DCACHE_SET_WIDTH-1:0] tag_rindex;
   reg [OPTION_DCACHE_SET_WIDTH-1:0]  tag_windex;

   // The data from the tag memory
   wire [TAGMEM_WIDTH-1:0] 	      tag_dout;
   wire [TAG_LRU_WIDTH_BITS-1:0]      tag_lru_out;
   wire [TAGMEM_WAY_WIDTH-1:0] 	      tag_way_out [OPTION_DCACHE_WAYS-1:0];

   // The data to the tag memory
   wire [TAGMEM_WIDTH-1:0] 	      tag_din;
   reg [TAG_LRU_WIDTH_BITS-1:0]       tag_lru_in;
   reg [TAGMEM_WAY_WIDTH-1:0] 	      tag_way_in [OPTION_DCACHE_WAYS-1:0];

   reg [TAGMEM_WAY_WIDTH-1:0] 	      tag_way_save[OPTION_DCACHE_WAYS-1:0];

   // Whether to write to the tag memory in this cycle
   reg 				      tag_we;

   // This is the tag we need to write to the tag memory during refill
   wire [TAG_WIDTH-1:0] 	      tag_wtag;

   // This is the tag we check against
   wire [TAG_WIDTH-1:0] 	      tag_tag;

   // Access to the way memories
   wire [WAY_WIDTH-3:0] 	      way_raddr[OPTION_DCACHE_WAYS-1:0];
   wire [WAY_WIDTH-3:0] 	      way_waddr[OPTION_DCACHE_WAYS-1:0];
   wire [OPTION_OPERAND_WIDTH-1:0]    way_din[OPTION_DCACHE_WAYS-1:0];
   wire [OPTION_OPERAND_WIDTH-1:0]    way_dout[OPTION_DCACHE_WAYS-1:0];
   reg [OPTION_DCACHE_WAYS-1:0]       way_we;

   // Does any way hit?
   wire 			      hit;
   wire [OPTION_DCACHE_WAYS-1:0]      way_hit;

   // This is the least recently used value before access the memory.
   // It is the value of current_lru_history that is combinationally
   // one hot encoded.
   // Used to select which way to replace during refill.
   wire [OPTION_DCACHE_WAYS-1:0]      current_lru;

   // Register that stores the LRU value from lru
   reg [OPTION_DCACHE_WAYS-1:0]       tag_save_lru;

   // The access vector to update the LRU history is the way that has
   // a hit or is refilled. It is also one-hot encoded.
   reg [OPTION_DCACHE_WAYS-1:0]       access;

   // The current encoded LRU history as read from tag memory.
   wire [TAG_LRU_WIDTH_BITS-1:0]      current_lru_history;
   // This is the encoded value of current LRU history after being combined
   // with the access vector.
   // This value is written back to tag memory if there is a hit or
   // refill.
   wire [TAG_LRU_WIDTH_BITS-1:0]      next_lru_history;

   // Intermediate signals to ease debugging
   wire [TAG_WIDTH-1:0]               check_way_tag [OPTION_DCACHE_WAYS-1:0];
   wire                               check_way_match [OPTION_DCACHE_WAYS-1:0];
   wire                               check_way_valid [OPTION_DCACHE_WAYS-1:0];

   reg 				      write_pending;

   // Extract index to read from snooped address
   wire [OPTION_DCACHE_SET_WIDTH-1:0] snoop_index;
   assign snoop_index = snoop_adr_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH];

   // Register that is high one cycle after the actual snoop event to
   // drive the comparison
   reg 				      snoop_check;
   // Register that stores the tag for one cycle
   reg [TAG_WIDTH-1:0] 		      snoop_tag;
   // Also store the index for one cycle, for the succeeding write access
   reg [OPTION_DCACHE_SET_WIDTH-1:0]  snoop_windex;

   // Snoop tag memory interface
   // Data out of tag memory
   wire [TAGMEM_WIDTH-1:0] 	      snoop_dout;
   // Each ways information in the tag memory
   wire [TAGMEM_WAY_WIDTH-1:0] 	      snoop_way_out [OPTION_DCACHE_WAYS-1:0];
   // Each ways tag in the tag memory
   wire [TAG_WIDTH-1:0] 	      snoop_check_way_tag [OPTION_DCACHE_WAYS-1:0];
   // Whether the tag matches the snoop tag
   wire                               snoop_check_way_match [OPTION_DCACHE_WAYS-1:0];
   // Whether the tag is valid
   wire                               snoop_check_way_valid [OPTION_DCACHE_WAYS-1:0];
   // Whether the way hits
   wire [OPTION_DCACHE_WAYS-1:0]      snoop_way_hit;
   // Whether any way hits
   wire 			      snoop_hit;

   assign snoop_hit_o = (OPTION_DCACHE_SNOOP != "NONE") ? snoop_hit : 0;

   genvar 			      i;

   // Ack the to LSU to indicate a Data Cache read is ready
   assign cpu_ack_o = ((read | refill) & hit & !write_pending |
		       refill_hit) & cpu_req_i & !snoop_hit;

   assign tag_rindex = cpu_adr_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH];

   assign tag_tag = cpu_adr_match_i[OPTION_DCACHE_LIMIT_WIDTH-1:WAY_WIDTH];
   assign tag_wtag = refill_adr_i[OPTION_DCACHE_LIMIT_WIDTH-1:WAY_WIDTH];

   assign cpu_err_o = 0;
   assign spr_bus_dat_o = 0;

   generate
      if (OPTION_DCACHE_WAYS >= 2) begin
         // Multiplex the LRU history from and to tag memory
         assign current_lru_history = tag_dout[TAG_LRU_MSB:TAG_LRU_LSB];
         assign tag_din[TAG_LRU_MSB:TAG_LRU_LSB] = tag_lru_in;
         assign tag_lru_out = tag_dout[TAG_LRU_MSB:TAG_LRU_LSB];
      end

      for (i = 0; i < OPTION_DCACHE_WAYS; i=i+1) begin : ways
	 assign way_raddr[i] = cpu_adr_i[WAY_WIDTH-1:2];
	 assign way_waddr[i] = write ? cpu_adr_match_i[WAY_WIDTH-1:2] :
			       refill_adr_i[WAY_WIDTH-1:2];
	 assign way_din[i] = way_wr_dat;

	 // compare stored tag with incoming tag and check valid bit
         assign check_way_tag[i] = tag_way_out[i][TAG_WIDTH-1:0];
         assign check_way_match[i] = (check_way_tag[i] == tag_tag);
         assign check_way_valid[i] = tag_way_out[i][TAGMEM_WAY_VALID];

         assign way_hit[i] = check_way_valid[i] & check_way_match[i];

         // Multiplex the way entries in the tag memory
         assign tag_din[(i+1)*TAGMEM_WAY_WIDTH-1:i*TAGMEM_WAY_WIDTH] = tag_way_in[i];
         assign tag_way_out[i] = tag_dout[(i+1)*TAGMEM_WAY_WIDTH-1:i*TAGMEM_WAY_WIDTH];

	 if (OPTION_DCACHE_SNOOP != "NONE") begin
	    // The same for the snoop tag memory
            assign snoop_way_out[i] = snoop_dout[(i+1)*TAGMEM_WAY_WIDTH-1:i*TAGMEM_WAY_WIDTH];

	    assign snoop_check_way_tag[i] = snoop_way_out[i][TAG_WIDTH-1:0];
	    assign snoop_check_way_match[i] = (snoop_check_way_tag[i] == snoop_tag);
	    assign snoop_check_way_valid[i] = snoop_way_out[i][TAGMEM_WAY_VALID];

	    assign snoop_way_hit[i] = snoop_check_way_valid[i] & snoop_check_way_match[i];
	 end
      end
   endgenerate

   assign hit = |way_hit;
   assign cache_hit_o = hit;

   assign snoop_hit = (OPTION_DCACHE_SNOOP != "NONE") &
		      |snoop_way_hit & snoop_check;

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

   assign next_refill_adr = (OPTION_DCACHE_BLOCK_WIDTH == 5) ?
			    {refill_adr_i[31:5], refill_adr_i[4:0] + 5'd4} : // 32 byte
			    {refill_adr_i[31:4], refill_adr_i[3:0] + 4'd4};  // 16 byte

   assign refill_done_o = refill_done;
   assign refill_done = refill_valid[next_refill_adr[OPTION_DCACHE_BLOCK_WIDTH-1:2]];
   assign refill_hit = refill_valid_r[cpu_adr_match_i[OPTION_DCACHE_BLOCK_WIDTH-1:2]] &
		       cpu_adr_match_i[OPTION_DCACHE_LIMIT_WIDTH-1:
				       OPTION_DCACHE_BLOCK_WIDTH] ==
		       refill_adr_i[OPTION_DCACHE_LIMIT_WIDTH-1:
				    OPTION_DCACHE_BLOCK_WIDTH] &
		       refill & !write_pending;

   assign refill = (state == REFILL);
   assign read = (state == READ);
   assign write = (state == WRITE);

   assign refill_o = refill;

   assign refill_req_o = read & cpu_req_i & !hit & !write_pending & refill_allowed_i | refill;

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
   integer w1;
   always @(posedge clk `OR_ASYNC_RST) begin
      if (rst) begin
	 state <= IDLE;
	 write_pending <= 0;
      end else if(dc_dbus_err_i) begin
	 state <= IDLE;
	 write_pending <= 0;
      end else begin
	 if (cpu_we_i)
	   write_pending <= 1;
	 else if (!cpu_req_i)
	   write_pending <= 0;

	 refill_valid_r <= refill_valid;

	 if (snoop_valid_i) begin
	    //
	    // If there is a snoop event, we need to store this
	    // information. This happens independent of whether we
	    // have a snoop tag memory or not.
	    //
	    snoop_check <= 1;
	    snoop_windex <= snoop_index;
	    snoop_tag <= snoop_adr_i[OPTION_DCACHE_LIMIT_WIDTH-1:WAY_WIDTH];
	 end else begin
	    snoop_check <= 0;
	 end

	 case (state)
	   IDLE: begin
	      if (invalidate) begin
		 // If there is an invalidation request
		 //
		 // Store address in invalidate_adr that is muxed to the tag
		 // memory write address
		 invalidate_adr <= spr_bus_dat_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH];

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
		 if (!hit & cpu_req_i & !write_pending & refill_allowed_i) begin
		    refill_valid <= 0;
		    refill_valid_r <= 0;

		    // Store the LRU information for correct replacement
                    // on refill. Always one when only one way.
                    tag_save_lru <= (OPTION_DCACHE_WAYS==1) | current_lru;

		    for (w1 = 0; w1 < OPTION_DCACHE_WAYS; w1 = w1 + 1) begin
		       tag_way_save[w1] <= tag_way_out[w1];
		    end

		    state <= REFILL;
		 end else if (cpu_we_i | write_pending) begin
		    state <= WRITE;
		 end else if (invalidate) begin
		    state <= IDLE;
		 end
	      end else if (!dc_enable_i | invalidate) begin
		 state <= IDLE;
	      end
	   end

	   REFILL: begin
	      if (refill_we_i) begin
		 refill_valid[refill_adr_i[OPTION_DCACHE_BLOCK_WIDTH-1:2]] <= 1;

		 if (refill_done)
		   state <= IDLE;
	      end
	      // Abort refill on snoop-hit
	      // TODO: only abort on snoop-hits to refill address
	      if (snoop_hit) begin
		 refill_valid <= 0;
		 refill_valid_r <= 0;
		 state <= IDLE;
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
		 // Store address in invalidate_adr that is muxed to the tag
		 // memory write address
		 invalidate_adr <= spr_bus_dat_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH];

		 state <= INVALIDATE;
	      end else begin
		 state <= IDLE;
	      end
	   end

	   default:
	     state <= IDLE;
	 endcase
      end
   end

   //
   // This is the combinational part of the state machine that
   // interfaces the tag and way memories.
   //
   integer w2;
   always @(*) begin
      // Default is to keep data, don't write and don't access
      tag_lru_in = tag_lru_out;
      for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
         tag_way_in[w2] = tag_way_out[w2];
      end

      tag_we = 1'b0;
      way_we = {(OPTION_DCACHE_WAYS){1'b0}};

      access = {(OPTION_DCACHE_WAYS){1'b0}};

      way_wr_dat = refill_dat_i;

      // The default is (of course) not to acknowledge the invalidate
      invalidate_ack = 1'b0;

      if (snoop_hit) begin
	 // This is the write access
	 tag_we = 1'b1;
	 tag_windex = snoop_windex;
	 for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
	    if (snoop_way_hit[w2]) begin
	       tag_way_in[w2] = 0;
	    end else begin
	       tag_way_in[w2] = snoop_way_out[w2];
	    end
	 end
      end else begin
	 //
	 // The tag mem is written during reads and writes to write
	 // the lru info and during refill and invalidate.
	 //
	 tag_windex = read | write ?
		      cpu_adr_match_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH] :
		      (state == INVALIDATE) ? invalidate_adr :
		      refill_adr_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH];

	 case (state)
	   IDLE: begin
	      //
	      // When idle we can always acknowledge the invalidate as it
	      // has the highest priority in handling. When something is
	      // changed on the state machine handling above this needs
	      // to be changed.
	      //
	      invalidate_ack = 1'b1;
	   end

	   READ: begin
	      if (hit) begin
		 //
		 // We got a hit. The LRU module gets the access
		 // information. Depending on this we update the LRU
		 // history in the tag.
		 //
		 access = way_hit;

		 // This is the updated LRU history after hit
		 tag_lru_in = next_lru_history;

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

		 // Only write data to way ram if we have a valid cacheline
		 way_we = way_hit;

		 tag_lru_in = next_lru_history;

		 tag_we = 1'b1;
	      end
	   end

	   REFILL: begin
	      if (refill_we_i) begin
		 //
		 // Write the data to the way that is replaced (which is
		 // the LRU)
		 //
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

		    tag_we = 1'b1;
		 end

		 //
		 // After refill update the tag memory entry of the
		 // filled way with the LRU history, the tag and set
		 // valid to 1.
		 //
		 if (refill_done) begin
		    for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
		       tag_way_in[w2] = tag_way_save[w2];
                       if (tag_save_lru[w2]) begin
			  tag_way_in[w2] = { 1'b1, tag_wtag };
                       end
                    end
                    tag_lru_in = next_lru_history;

		    tag_we = 1'b1;
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

	      tag_we = 1'b1;
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
		 .ENABLE_BYPASS(1)
		 )
	 way_data_ram
	       (
		// Outputs
		.dout			(way_dout[i]),
		// Inputs
		.clk			(clk),
		.raddr			(way_raddr[i][WAY_WIDTH-3:0]),
		.re			(1'b1),
		.waddr			(way_waddr[i][WAY_WIDTH-3:0]),
		.we			(way_we[i]),
		.din			(way_din[i][31:0]));

      end

      if (OPTION_DCACHE_WAYS >= 2) begin : gen_u_lru
         mor1kx_cache_lru
           #(.NUMWAYS(OPTION_DCACHE_WAYS))
         u_lru(
	       // Outputs
	       .update			(next_lru_history),	 // Templated
	       .lru_pre			(current_lru),		 // Templated
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
       .ENABLE_BYPASS(OPTION_DCACHE_SNOOP != "NONE")
     )
   tag_ram
     (
      // Outputs
      .dout				(tag_dout[TAGMEM_WIDTH-1:0]),
      // Inputs
      .clk				(clk),
      .raddr				(tag_rindex),
      .re				(1'b1),
      .waddr				(tag_windex),
      .we				(tag_we),
      .din				(tag_din));

generate
if (OPTION_DCACHE_SNOOP != "NONE") begin
   mor1kx_simple_dpram_sclk
     #(
       .ADDR_WIDTH(OPTION_DCACHE_SET_WIDTH),
       .DATA_WIDTH(TAGMEM_WIDTH),
       .ENABLE_BYPASS(1)
       )
   snoop_tag_ram
     (
      // Outputs
      .dout			(snoop_dout[TAGMEM_WIDTH-1:0]),
      // Inputs
      .clk			(clk),
      .raddr			(snoop_index),
      .re			(1'b1),
      .waddr			(tag_windex),
      .we			(tag_we),
      .din			(tag_din));
end
endgenerate


/*----------------Formal Checking-----------------*/

`ifdef FORMAL

`ifdef DCACHE
`define ASSUME assume
`else
`define ASSUME assert
`endif

   reg f_past_valid;
   initial f_past_valid = 1'b0;
   initial assume (rst);

   always @(posedge clk)
      f_past_valid <= 1'b1;
   always @(*)
      if (!f_past_valid)
         assume (rst);

//-----------Assumptions on Inputs-----------

   always @(posedge clk) begin
      if (cpu_req_i)
         `ASSUME (dc_access_i);
   end

//-------------Assertions--------------------

`ifdef DCACHE

//----------Verifying functionality---------

//Case 1: Refill followed by read

   (* anyconst *) wire [OPTION_OPERAND_WIDTH-1:0] f_refill_addr;
   reg [OPTION_OPERAND_WIDTH-1:0] f_refill_data;
   wire f_this_refill;
   reg f_refilled;
   initial f_refilled = 1'b0;
   assign f_this_refill = (refill_adr_i == f_refill_addr) && refill_o;

   //Refilling
   always @(posedge clk) begin
      if ($past(f_this_refill) && (f_refill_data == refill_dat_i)
          && !$past(write_pending) && $past(refill_allowed_i)
          && !$past(cache_hit_o)&& $past(cpu_req_i)
          && f_past_valid && !$past(rst) &&
          $past(state) == READ) begin
         assert (refill);
         f_refilled <= 1'b1;
         assert ($onehot(way_we));
      end
   end

   //Read: Asserting if f_refill_data is returned if the
   //      cpu requests for same address f_refill_addr.
   always @(posedge clk) begin
      if ($rose(f_refilled) && (cpu_adr_match_i == f_refill_addr)
         && cache_hit_o && f_past_valid && !$past(rst)) begin
         assert (cpu_dat_o == f_refill_data);
         assert (read);
         assert (cpu_ack_o);
      end
   end

   reg f_after_invalidate;
   initial f_after_invalidate = 1'b0;

   //Invalidation : Checking if ways of set have invalid tag bit
   //               on set invalidation.
   always @(posedge clk) begin
      if ($past(invalidate) && !$past(refill) && f_past_valid &&
         $past(spr_bus_dat_i) == f_refill_addr[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH]
         && $past(f_refilled) && !$past(f_refilled,2)) begin
         assert (spr_bus_ack_o);
         assert (invalidate);
         assert (!cpu_ack_o);
         assert (tag_we);
         assert (!tag_din[TAGMEM_WAY_VALID]);
         f_after_invalidate <= 1;
      end
   end

   //There shouldn't be any cache hit for f_refill_addr after invalidation.
   always @(posedge clk)
      if (cpu_adr_match_i == f_refill_addr && $rose(f_after_invalidate)
          && f_past_valid)
         assert (!cache_hit_o);

//Case 2: Write followed by read

   (* anyconst *) wire [OPTION_OPERAND_WIDTH-1:0] f_write_addr;
   (* anyconst *) reg [OPTION_OPERAND_WIDTH-1:0] f_write_data;
   wire f_this_write;
   reg f_written;
   initial f_written = 1'b0;
   assign f_this_write = (cpu_adr_match_i == f_write_addr);

   //Write
   always @(posedge clk)
      if (f_this_write && (f_write_data == cpu_dat_i)
          && $past(cpu_we_i) && f_past_valid && !$past(rst)
          && !$past(invalidate) && cpu_bsel_i == 4'hf
          && !$past(write_pending) && !$past(dc_dbus_err_i)
          && !invalidate && !dc_dbus_err_i && $past(state) == IDLE
          && $onehot(way_hit) && cpu_req_i) begin
         assert (write);
         assert ($onehot(way_we));
         f_written <= 1;
       end

   //Read
   always @(posedge clk)
      if (f_past_valid && $past(f_written) && !$past(f_written,2)
         && $past(cpu_adr_i) == f_write_addr && (cpu_adr_match_i == f_write_addr)
         && !write_pending && cpu_req_i && !$past(rst)
         && cache_hit_o && !$past(way_we)) begin
         assert (cpu_dat_o == f_write_data);
      end

   reg f_invalid;
   initial f_invalid = 1'b0;

   //Invalidate f_write_addr
   always @(posedge clk)
      if (!$past(invalidate,2) && $past(invalidate) && f_past_valid &&
         $past(spr_bus_dat_i) == f_write_addr[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH]
         && $rose(f_written) && !$past(dc_dbus_err_i) && !$past(cpu_we_i)) begin
         assert (spr_bus_ack_o);
         assert (!cpu_ack_o);
         assert (tag_we);
         assert (!tag_din[TAGMEM_WAY_VALID]);
         f_invalid <= 1'b1;
      end

   //No cache hit for invalidated address
   always @(posedge clk)
      if (f_past_valid && cpu_adr_match_i == f_write_addr
          && $rose(f_invalid) && f_past_valid)
         assert (!cache_hit_o);

`endif

//-------------DCACHE PROPERTIES-------------------

   //Cache hit in read state updates lru access variable
   always @(posedge clk) begin
      if (f_past_valid && !$past(rst) && way_hit[0]
          && $onehot(way_hit) && read)
         assert (access == way_hit[0]);
   end

   //Way ram writes only on cpu write request or refill request.
   always @(posedge clk)
      if (way_we == way_hit && $onehot(way_hit) &&
          f_past_valid && !$past(rst) && !dc_dbus_err_i)
         assert (cpu_we_i || write_pending || refill_we_i ||
                 $past(write_pending));

   //CPU acknowledgement is given only if cache fulfills cpu's request.
   always @(posedge clk)
      if (cpu_ack_o)
         assert (cpu_req_i);

   //CPU receives acknowledgement only on cache hits or refill hits.
   always @(posedge clk)
      if (cpu_ack_o && f_past_valid && !$past(rst))
         assert (cache_hit_o || refill_hit);

   //Back to back writes should keep write pending high
   always @(posedge clk)
      if (f_past_valid && !$past(rst) && $past(cpu_we_i) && cpu_we_i
         && !$past(dc_dbus_err_i) && cache_hit_o &&
         !$past(cpu_we_i,2) && $past(rst,2))
         assert (write_pending);
   always @(posedge clk)
      if (write_pending && f_past_valid && !$past(rst))
         assert ($past(cpu_we_i) || $past(write_pending));

   //Write is successful only if there is cache hit
   always @(*)
      if ($onehot(way_we) && write)
         assert (cache_hit_o);

   //Cache writes should update both way and tag memories
   always @(posedge clk)
      if (write && cpu_req_i && cache_hit_o && $onehot(way_hit) && f_past_valid)
         assert (tag_we && $onehot(way_we));

   //Refill data shouldn't be written while doing write operation
   always @(posedge clk)
      if (write && f_past_valid && cpu_dat_i != refill_dat_i &&
          !$past(rst) && cpu_bsel_i == 4'hf)
         assert (way_wr_dat != refill_dat_i);

   //Dcache triggers to refill state only if there is cache miss
   always @(posedge clk)
      if ($rose(refill_o) && f_past_valid && !$past(rst))
         assert (!$past(cache_hit_o));

   //Refill hit shouldn't happen in any state other than refill
   always @(posedge clk)
      if (refill_hit && f_past_valid && !$past(rst))
         assert (state != READ && state != WRITE && state != INVALIDATE && state != IDLE);

   //Refilling should always update way ram
   always @(*)
      if (refill_o && refill_we_i && $onehot(tag_save_lru))
         assert ($onehot(way_we));

   //Before refilling tag should be invalidated
   always @(*)
      if (refill_o && !refill_valid && refill_we_i)
         assert (tag_we);

//---------INVALIDATION AND SPR BUS ----------

   //Dcache invalidation is initiated only if the spr request
   // is for block flush or block invalidate
   always @(posedge clk)
      if (invalidate)
         assert (spr_bus_addr_i == `OR1K_SPR_DCBFR_ADDR |
                  spr_bus_addr_i == `OR1K_SPR_DCBIR_ADDR);

   //Invalidate should acknowledge only if spr has some invalidate request
   //or if cache remains in either idle or invalidate state.
   always @(posedge clk)
      if ($rose(invalidate_ack) && f_past_valid && !$past(rst))
         assert (state == INVALIDATE || state == IDLE || $past(invalidate));

   reg f_1st_inv;
   initial f_1st_inv = 1'b0;

   //Checking back to back invalidation writes
   always @(posedge clk)
      if ($past(invalidate) && invalidate && f_past_valid && !$past(rst)
         && $past(rst,2) && !$past(dc_dbus_err_i) && !$past(cpu_we_i,2)
         && !dc_dbus_err_i && !rst) begin
         assert (tag_we);
         f_1st_inv <= 1'b1;
      end
   always @(posedge clk)
      if ($rose(f_1st_inv) && f_past_valid) begin
         assert (tag_we);
         assert (invalidate_ack);
      end

   //SPR acknowledgement is valid only if there is invalidate acknowledgement.
   always @(posedge clk)
      if (spr_bus_ack_o)
         assert (invalidate_ack);

   //If invalidation and write arrives at same the clock invalidation wins over writing
   //Case 1: Just after reset
   always @(posedge clk)
      if ($past(invalidate) && f_past_valid && !$past(rst)
         && $past(cpu_we_i) && !$past(dc_dbus_err_i)
         && !$past(cpu_we_i,2) && $past(rst,2)) begin
         assert (write_pending);
         assert (invalidate_ack);
      end

   //Case 2:Invalidate and write signal arriving at same clock, not right after reset.
   //If cache is in read state and these signals arrive then write wins over invalidation.
   always @(posedge clk)
      if ($past(invalidate) && f_past_valid && !$past(rst)
          && $past(cpu_we_i) && !$past(dc_dbus_err_i) && !$past(cpu_we_i,2)
          && !$past(rst,2) && !$past(write_pending,2) && !$past(write_pending))
      assert (write_pending);

   fspr_slave #(
       .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH),
       .SLAVE("DCACHE")
       )
       u_f_icache_slave (
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

//----------------Cover-----------------

   //Cache Write-----------Trace 0
   always @(posedge clk)
      cover (state == WRITE && tag_we && $onehot(way_we) && f_past_valid && !$past(rst));

   //Invalidation----------Trace 1
   always @(posedge clk)
      cover (tag_we && state == INVALIDATE && !$past(rst) && f_past_valid);

   //Cache Read------------Trace 2
   always @(posedge clk)
      cover (state == READ && tag_we && cache_hit_o && cpu_ack_o && !$past(rst) && f_past_valid);

   //Refilling-------------Trace 3
   always @(posedge clk)
      cover (refill_o && $onehot(way_we) && refill_done && tag_we && !$past(rst) && f_past_valid);

`endif
endmodule
