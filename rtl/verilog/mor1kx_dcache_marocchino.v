////////////////////////////////////////////////////////////////////////
//                                                                    //
//  mor1kx_icache_marocchino                                          //
//                                                                    //
//  Description: Data CACHE implementation                            //
//               The variant is tightly coupled with                  //
//               MAROCCHINO LSU and DMMU                              //
//               (based on mor1kx_dcache)                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////
//                                                                    //
//   Copyright (C) 2012-2013 Stefan Kristiansson                      //
//                           stefan.kristiansson@saunalahti.fi        //
//                                                                    //
//                           Stefan Wallentowitz                      //
//                           stefan.wallentowitz@tum.de               //
//                                                                    //
//   Copyright (C) 2015 Andrey Bacherov                               //
//                      avbacherov@opencores.org                      //
//                                                                    //
//      This Source Code Form is subject to the terms of the          //
//      Open Hardware Description License, v. 1.0. If a copy          //
//      of the OHDL was not distributed with this file, You           //
//      can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt       //
//                                                                    //
////////////////////////////////////////////////////////////////////////

`include "mor1kx-defines.v"

module mor1kx_dcache_marocchino
#(
  parameter OPTION_OPERAND_WIDTH        = 32,
  parameter OPTION_DCACHE_BLOCK_WIDTH   =  5,
  parameter OPTION_DCACHE_SET_WIDTH     =  9,
  parameter OPTION_DCACHE_WAYS          =  2,
  parameter OPTION_DCACHE_LIMIT_WIDTH   = 32,
  parameter OPTION_DCACHE_SNOOP         = "NONE",
  parameter OPTION_DCACHE_CLEAR_ON_INIT =  0
)
(
  // clock & reset
  input                                 clk,
  input                                 rst,

  // pipe controls
  input                                 lsu_takes_load_i,
  input                                 lsu_takes_store_i,
  input                                 pipeline_flush_i,

  // configuration
  input                                 enable_i,

  // exceptions
  input                                 lsu_excepts_any_i,
  input                                 dbus_err_instant_i,

  // Regular operation
  //  # addresses and "DCHACHE inhibit" flag
  input      [OPTION_OPERAND_WIDTH-1:0] virt_addr_i,
  input      [OPTION_OPERAND_WIDTH-1:0] virt_addr_cmd_i,
  input      [OPTION_OPERAND_WIDTH-1:0] phys_addr_cmd_i,
  input                                 dmmu_cache_inhibit_i,
  //  # DCACHE regular answer
  output                                dc_access_o,
  output                                dc_ack_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] dc_dat_o,
  //  # STORE format / store data / do|cancel storing
  input                           [3:0] dbus_bsel_i,
  input      [OPTION_OPERAND_WIDTH-1:0] dbus_sdat_i,
  input                                 dc_store_allowed_i,
  input                                 dbus_swa_discard_i,

  // re-fill
  output                                dc_refill_req_o,
  input                                 dc_refill_allowed_i,
  output     [OPTION_OPERAND_WIDTH-1:0] next_refill_adr_o,
  output                                refill_last_o,
  input      [OPTION_OPERAND_WIDTH-1:0] dbus_dat_i,
  input                                 dbus_ack_i,

  // SNOOP
  // Snoop address
  input      [OPTION_OPERAND_WIDTH-1:0] snoop_adr_i,
  // Snoop event in this cycle
  input                                 snoop_event_i,
  // Whether the snoop hit. If so, there will be no tag memory write
  // this cycle. The LSU may need to stall the pipeline.
  output                                snoop_hit_o,

  // SPR interface
  input                          [15:0] spr_bus_addr_i,
  input                                 spr_bus_we_i,
  input                                 spr_bus_stb_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_i,
  output     [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o,
  output reg                            spr_bus_ack_o
);

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


  // States
  localparam  [4:0] DC_IDLE       = 5'b00001,
                    DC_READ       = 5'b00010,
                    DC_WRITE      = 5'b00100,
                    DC_REFILL     = 5'b01000,
                    DC_INVALIDATE = 5'b10000;
  // FSM state register
  reg [4:0] dc_state;
  // FSM state signals
  wire dc_read       = (dc_state == DC_READ);
  wire dc_write      = (dc_state == DC_WRITE);
  wire dc_refill     = (dc_state == DC_REFILL);
  wire dc_invalidate = (dc_state == DC_INVALIDATE);


  reg                [OPTION_OPERAND_WIDTH-1:0] way_wr_dat;

  reg                [OPTION_OPERAND_WIDTH-1:0] curr_refill_adr;
  reg                                           refill_hit_r;     // 1-clock length
  reg                                           refill_hit_was_r; // from re-fill-hit to re-fill-complete
  reg  [(1<<(OPTION_DCACHE_BLOCK_WIDTH-2))-1:0] refill_done;

  // The index we read and write from tag memory
  wire [OPTION_DCACHE_SET_WIDTH-1:0] tag_rindex;
  reg  [OPTION_DCACHE_SET_WIDTH-1:0] tag_windex;

  // The data from the tag memory
  wire       [TAGMEM_WIDTH-1:0] tag_dout;
  wire   [TAGMEM_WAY_WIDTH-1:0] tag_way_out [OPTION_DCACHE_WAYS-1:0];

  // The data to the tag memory
  wire      [TAGMEM_WIDTH-1:0] tag_din;
  reg [TAG_LRU_WIDTH_BITS-1:0] tag_lru_in;
  reg   [TAGMEM_WAY_WIDTH-1:0] tag_way_in [OPTION_DCACHE_WAYS-1:0];

  reg   [TAGMEM_WAY_WIDTH-1:0] tag_way_save[OPTION_DCACHE_WAYS-1:0];

  // Whether to write to the tag memory in this cycle
  reg                          tag_we;

  // WAYs related
  wire [OPTION_OPERAND_WIDTH-1:0] way_dout[OPTION_DCACHE_WAYS-1:0];
  reg    [OPTION_DCACHE_WAYS-1:0] way_we; // Write signals per way
  wire   [OPTION_DCACHE_WAYS-1:0] way_re; // Read signals per way

  // Does any way hit?
  wire                          dc_hit;
  wire [OPTION_DCACHE_WAYS-1:0] way_hit;

  // This is the least recently used value before access the memory.
  // Those are one hot encoded.
  wire [OPTION_DCACHE_WAYS-1:0] lru;

  // Register that stores the LRU value from lru
  reg  [OPTION_DCACHE_WAYS-1:0] tag_save_lru;


  // The access vector to update the LRU history is the way that has
  // a hit or is refilled. It is also one-hot encoded.
  reg  [OPTION_DCACHE_WAYS-1:0] access_lru_history;
  // The current LRU history as read from tag memory and the update
  // value after we accessed it to write back to tag memory.
  wire [TAG_LRU_WIDTH_BITS-1:0] current_lru_history;
  wire [TAG_LRU_WIDTH_BITS-1:0] next_lru_history;


  // Extract index to read from snooped address
  wire [OPTION_DCACHE_SET_WIDTH-1:0] snoop_index;
  assign snoop_index = snoop_adr_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH];

  // Register that is high one cycle after the actual snoop event to
  // drive the comparison
  reg                                snoop_check;
  // Register that stores the tag for one cycle
  reg                [TAG_WIDTH-1:0] snoop_tag;
  // Also store the index for one cycle, for the succeeding write access
  reg  [OPTION_DCACHE_SET_WIDTH-1:0] snoop_windex;
  // Snoop Tag RAM input
  wire [OPTION_DCACHE_SET_WIDTH-1:0] snoop_rindex;

  // Snoop tag memory interface
  // Data out of tag memory
  wire       [TAGMEM_WIDTH-1:0] snoop_dout;
  // Each ways information in the tag memory
  wire   [TAGMEM_WAY_WIDTH-1:0] snoop_way_out [OPTION_DCACHE_WAYS-1:0];
  // Whether the way hits
  wire [OPTION_DCACHE_WAYS-1:0] snoop_way_hit;


  genvar                        i;



  wire dc_check_limit_width;

  generate
  // Addresses 0x8******* are treated as non-cacheble regardless DMMU's flag.
  if (OPTION_DCACHE_LIMIT_WIDTH == OPTION_OPERAND_WIDTH)
    assign dc_check_limit_width = 1'b1;
  else if (OPTION_DCACHE_LIMIT_WIDTH < OPTION_OPERAND_WIDTH)
    assign dc_check_limit_width =
      (phys_addr_cmd_i[OPTION_OPERAND_WIDTH-1:OPTION_DCACHE_LIMIT_WIDTH] == 0);
  else begin
    initial begin
      $display("DCACHE ERROR: OPTION_ICACHE_LIMIT_WIDTH > OPTION_OPERAND_WIDTH");
      $finish();
    end
  end
  endgenerate


  //
  //   If DCACHE is in state read/write/refill it automatically means that
  // DCACHE is enabled (see dc_takes_load and dc_takes_store).
  //
  //   So, locally we use short variant of dc-access
  wire   dc_access   = dc_check_limit_width & ~dmmu_cache_inhibit_i;
  //   While for output the full variant is used
  assign dc_access_o = (dc_read | dc_write | dc_refill) & dc_access;

  // if requested data were fetched befire snoop-hit, it is valid
  assign dc_ack_o = (dc_access & dc_read & dc_hit & ~snoop_hit_o) | refill_hit_r;

  // re-fill reqest is allowed only after completion snoop-processing
  // see refill-allowed in LSU
  assign dc_refill_req_o = dc_access & dc_read & ~dc_hit & ~snoop_hit_o;



  generate
  if (OPTION_DCACHE_WAYS >= 2) begin
    // Multiplex the LRU history from and to tag memory
    assign current_lru_history = tag_dout[TAG_LRU_MSB:TAG_LRU_LSB];
    assign tag_din[TAG_LRU_MSB:TAG_LRU_LSB] = tag_lru_in;
  end

  for (i = 0; i < OPTION_DCACHE_WAYS; i=i+1) begin : ways
    // Multiplex the way entries in the tag memory
    assign tag_din[(i+1)*TAGMEM_WAY_WIDTH-1:i*TAGMEM_WAY_WIDTH] = tag_way_in[i];
    assign tag_way_out[i] = tag_dout[(i+1)*TAGMEM_WAY_WIDTH-1:i*TAGMEM_WAY_WIDTH];

    // compare stored tag with incoming tag and check valid bit
    assign way_hit[i] = tag_way_out[i][TAGMEM_WAY_VALID] &
      (tag_way_out[i][TAG_WIDTH-1:0] == phys_addr_cmd_i[OPTION_DCACHE_LIMIT_WIDTH-1:WAY_WIDTH]); // hit detection

    // The same for the snoop tag memory
    if (OPTION_DCACHE_SNOOP != "NONE") begin
      assign snoop_way_out[i] = snoop_dout[(i+1)*TAGMEM_WAY_WIDTH-1:i*TAGMEM_WAY_WIDTH];
      // compare stored tag with incoming tag and check valid bit
      assign snoop_way_hit[i] = snoop_way_out[i][TAGMEM_WAY_VALID] &
        (snoop_way_out[i][TAG_WIDTH-1:0] == snoop_tag);
    end // DCACHE snoop
    else begin
      assign snoop_way_hit[i] = 1'b0; // no snoop
      assign snoop_way_out[i] = {TAGMEM_WAY_WIDTH{1'b0}}; // no snoop
    end
  end // loop by ways
  endgenerate

  assign dc_hit = |way_hit;

  assign snoop_hit_o = (|snoop_way_hit) & snoop_check;

  integer w0;
  always @(*) begin
    dc_dat_o = {OPTION_OPERAND_WIDTH{1'b0}};
    // Put correct way on the data port
    for (w0 = 0; w0 < OPTION_DCACHE_WAYS; w0 = w0 + 1) begin
      if (way_hit[w0] | (refill_hit_r & tag_save_lru[w0])) begin
        dc_dat_o = way_dout[w0];
      end
    end
  end



  assign next_refill_adr_o = (OPTION_DCACHE_BLOCK_WIDTH == 5) ?
    {curr_refill_adr[31:5], curr_refill_adr[4:0] + 5'd4} : // 32 byte = (8 words x 32 bits/word) = (4 words x 64 bits/word)
    {curr_refill_adr[31:4], curr_refill_adr[3:0] + 4'd4};  // 16 byte = (4 words x 32 bits/word) = (2 words x 64 bits/word)

  assign refill_last_o = refill_done[next_refill_adr_o[OPTION_DCACHE_BLOCK_WIDTH-1:2]];



  /*
   * SPR bus interface
   *  # Only invalidate command is implemented
   *  # In MAROCCHINO pipeline l.mf(t)spr instructions are executed
   *    if pipeline is stalled.
   */

  assign spr_bus_dat_o = {OPTION_OPERAND_WIDTH{1'b0}};

  // An invalidate request is either a block flush or a block invalidate
  wire spr_bus_dc_invalidate = spr_bus_stb_i & spr_bus_we_i &
                               ((spr_bus_addr_i == `OR1K_SPR_DCBFR_ADDR) |
                                (spr_bus_addr_i == `OR1K_SPR_DCBIR_ADDR));



  /*
   * Cache FSM controls
   */

  // try load
  wire dc_takes_load  = lsu_takes_load_i  & enable_i;

  // try store
  wire dc_takes_store = lsu_takes_store_i & enable_i;

  // force idle state
  wire dc_force_idle  = lsu_excepts_any_i | pipeline_flush_i;



  /*
   * Cache FSM
   */

  integer w1;

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      dc_state            <= DC_IDLE;  // on reset
      curr_refill_adr     <= {OPTION_OPERAND_WIDTH{1'b0}};  // on reset
      refill_hit_r        <= 1'b0;  // on reset
      refill_hit_was_r    <= 1'b0;  // on reset
      refill_done         <= 0;     // on reset
      snoop_check         <= 1'b0;  // on reset
      snoop_tag           <= {TAG_WIDTH{1'b0}};               // on reset
      snoop_windex        <= {OPTION_DCACHE_SET_WIDTH{1'b0}}; // on reset
      tag_save_lru        <= {OPTION_DCACHE_WAYS{1'b0}};      // on reset
      for (w1 = 0; w1 < OPTION_DCACHE_WAYS; w1 = w1 + 1) begin
        tag_way_save[w1] <= {TAGMEM_WAY_WIDTH{1'b0}};
      end
      spr_bus_ack_o       <= 1'b0; // on reset
    end
    else begin
      // snoop processing
      if (snoop_event_i) begin
        //
        // If there is a snoop event, we need to store this
        // information. This happens independent of whether we
        // have a snoop tag memory or not.
        //
        snoop_check  <= 1'b1;
        snoop_windex <= snoop_index; // on snoop-event
        snoop_tag    <= snoop_adr_i[OPTION_DCACHE_LIMIT_WIDTH-1:WAY_WIDTH];
      end
      else begin
        snoop_check  <= 1'b0;
      end

      // states switching
      // synthesis parallel_case full_case
      case (dc_state)
        DC_IDLE: begin
          spr_bus_ack_o <= 1'b0; // idling
          // next states
          if (dc_force_idle | snoop_hit_o) // keep idle (overcome advance commands)
            dc_state <= DC_IDLE;
          else if (spr_bus_dc_invalidate)
            dc_state <= DC_INVALIDATE;
          else if (dc_takes_load)
            dc_state <= DC_READ;
          else if (dc_takes_store)
            dc_state <= DC_WRITE;
        end

        DC_READ: begin
          if (dc_force_idle) // abort read access
            dc_state <= DC_IDLE;
          else if (snoop_hit_o)
            dc_state <= DC_READ;
          else if (dc_access) begin
            if (~dc_hit) begin // re-fill request
              if (dc_refill_allowed_i) begin
                // Store the LRU information for correct replacement
                // on re-fill. Always one when only one way.
                tag_save_lru <= (OPTION_DCACHE_WAYS == 1) | lru;  // read -> re-fill
                // store tag state
                for (w1 = 0; w1 < OPTION_DCACHE_WAYS; w1 = w1 + 1) begin
                  tag_way_save[w1] <= tag_way_out[w1];
                end
                // 1st re-fill addrress
                curr_refill_adr  <= phys_addr_cmd_i;  // read -> re-fill
                refill_hit_was_r <= 1'b0;             // read -> re-fill
                // to RE-FILL
                dc_state <= DC_REFILL;
              end // re-fill allowed
            end // no hit
            else if (dc_takes_store) // dc-access & load-hit & new-command-is-store
              dc_state <= DC_WRITE;
            else if (~dc_takes_load)
              dc_state <= DC_IDLE;
          end
          else if (dc_takes_store) // not-dc-access
            dc_state <= DC_WRITE;
          else if (~dc_takes_load)
            dc_state <= DC_IDLE;
        end

        DC_WRITE: begin
          if (dc_force_idle) // abort write access
            dc_state <= DC_IDLE;
          else if (snoop_hit_o)
            dc_state <= DC_WRITE;
          else if (dc_access & dc_hit) begin
            if (dc_store_allowed_i | dbus_swa_discard_i) begin
              if (dc_takes_load)
                dc_state <= DC_READ;
              else if (~dc_takes_store)
                dc_state <= DC_IDLE;
            end // store-hit & (do store OR diascard l.swa)
          end
          else if (dc_takes_load) // ~dc-access
            dc_state <= DC_READ;
          else if (~dc_takes_store)
            dc_state <= DC_IDLE;
        end

        DC_REFILL: begin
          refill_hit_r <= 1'b0;
          // 1) Abort re-fill on snoop-hit
          //    TODO: only abort on snoop-hits to re-fill address
          // 2) In according with WISHBONE-B3 rule 3.45:
          //    "SLAVE MUST NOT assert more than one of ACK, ERR or RTY"
          if (snoop_hit_o) begin
            refill_hit_was_r <= 1'b0;  // on snoop-hit during re-fill
            refill_done      <= 0;     // on snoop-hit during re-fill
            dc_state         <= refill_hit_was_r ? DC_IDLE : DC_READ;  // on snoop-hit during re-fill
          end
          else if (dbus_ack_i) begin
            if (refill_last_o) begin
              refill_hit_was_r <= 1'b0;  // on last re-fill
              refill_done      <= 0;     // on last re-fill
              tag_save_lru     <= {OPTION_DCACHE_WAYS{1'b0}}; // on last re-fill
              dc_state         <= DC_IDLE;  // on last re-fill
            end
            else begin
              refill_hit_r     <= (refill_done == 0); // 1st re-fill is requested insn
              refill_hit_was_r <= (refill_done == 0) | refill_hit_was_r; // 1st re-fill
              refill_done[curr_refill_adr[OPTION_DCACHE_BLOCK_WIDTH-1:2]] <= 1'b1; // current re-fill
              curr_refill_adr <= next_refill_adr_o;
            end // last or regulat
          end // snoop-hit / dbus-ack
          else if (dbus_err_instant_i) begin  // abort re-fill
            refill_hit_was_r <= 1'b0;     // on dbus error during re-fill
            refill_done      <= 0;        // on dbus error during re-fill
            tag_save_lru     <= {OPTION_DCACHE_WAYS{1'b0}}; // on dbus error during re-fill
            dc_state         <= DC_IDLE;  // on dbus error during re-fill
          end
        end // re-fill

        DC_INVALIDATE: begin
          if (~snoop_hit_o) begin // wait till snoop-inv completion
            dc_state      <= DC_IDLE; // invalidate -> idling
            spr_bus_ack_o <= 1'b1;    // invalidate -> idling
          end
        end

        default: begin
          dc_state            <= DC_IDLE;  // on default
          curr_refill_adr     <= {OPTION_OPERAND_WIDTH{1'b0}};  // on default
          refill_hit_r        <= 1'b0;  // on default
          refill_hit_was_r    <= 1'b0;  // on default
          refill_done         <= 0;     // on default
          snoop_check         <= 1'b0;  // on default
          snoop_tag           <= {TAG_WIDTH{1'b0}}; // on default
          snoop_windex        <= {OPTION_DCACHE_SET_WIDTH{1'b0}}; // on default
          tag_save_lru        <= {OPTION_DCACHE_WAYS{1'b0}}; // on default
          for (w1 = 0; w1 < OPTION_DCACHE_WAYS; w1 = w1 + 1) begin
            tag_way_save[w1] <= {TAGMEM_WAY_WIDTH{1'b0}};
          end
        end
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
    tag_lru_in = current_lru_history;
    for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
      tag_way_in[w2] = tag_way_out[w2];
    end

    tag_we = 1'b0;
    way_we = {OPTION_DCACHE_WAYS{1'b0}};

    access_lru_history = {OPTION_DCACHE_WAYS{1'b0}};

    //  # As way size is equal to page one we able to use ether
    //    physical or virtual indexing. We use virual indexing because
    //    it isn't changed by DMMU on/off.
    tag_windex = virt_addr_cmd_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH]; // by default
    way_wr_dat = dbus_sdat_i; // by default

    if (snoop_hit_o) begin
      // This is the write access
      tag_we     = 1'b1;
      tag_windex = snoop_windex;
      for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
        tag_way_in[w2] = snoop_way_out[w2] & {TAGMEM_WAY_WIDTH{~snoop_way_hit[w2]}}; // zero where hit
      end
    end
    else begin
      // synthesis parallel_case full_case
      case (dc_state)
        DC_READ: begin
          if (dc_access & dc_hit & ~dc_force_idle) begin // on read-hit
            // tag write address
            //  # As way size is equal to page one we able to use ether
            //    physical or virtual indexing. We use virual indexing because
            //    it isn't changed by DMMU on/off.
            tag_windex = virt_addr_cmd_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH]; // on read (LRU history update)
            // We got a hit. The LRU module gets the access
            // information. Depending on this we update the LRU
            // history in the tag.
            access_lru_history = way_hit;
            // This is the updated LRU history after hit
            tag_lru_in = next_lru_history;
            // To store LRU history
            tag_we = 1'b1;
          end
        end

        DC_WRITE: begin
          if (dc_access & dc_hit & dc_store_allowed_i & ~dc_force_idle) begin // on write-hit
            // write addresses
            //  # As way size is equal to page one we able to use ether
            //    physical or virtual indexing. We use virual indexing because
            //    it isn't changed by DMMU on/off.
            tag_windex = virt_addr_cmd_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH]; // on write-hit
            way_wr_dat = dbus_sdat_i;                                            // on write-hit
            // Mux cache output with write data
            if (~dbus_bsel_i[3]) way_wr_dat[31:24] = dc_dat_o[31:24];
            if (~dbus_bsel_i[2]) way_wr_dat[23:16] = dc_dat_o[23:16];
            if (~dbus_bsel_i[1]) way_wr_dat[15:8]  = dc_dat_o[15: 8];
            if (~dbus_bsel_i[0]) way_wr_dat[7:0]   = dc_dat_o[ 7: 0];
            // select way for write
            way_we = way_hit; // on write
            // update lsu history
            tag_lru_in = next_lru_history;
            // ---
            tag_we = 1'b1; // on write
          end
        end

        DC_REFILL: begin
          // In according with WISHBONE-B3 rule 3.45:
          // "SLAVE MUST NOT assert more than one of ACK, ERR or RTY"
          if (dbus_ack_i) begin // on re-fill
            // write addresses
            tag_windex = curr_refill_adr[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH]; // on re-fill
            way_wr_dat = dbus_dat_i;                                             // on re-fill
            //
            // Write the data to the way that is replaced
            // (which is the LRU)
            //
            way_we = tag_save_lru; // on re-fill
            // Invalidate the way on the first write
            if (refill_done == 0) begin
              for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
                if (tag_save_lru[w2]) begin
                  tag_way_in[w2][TAGMEM_WAY_VALID] = 1'b0;
                end
              end
              // ---
              tag_we = 1'b1;
            end
            //
            // After re-fill update the tag memory entry of the
            // filled way with the LRU history, the tag and set
            // valid to 1.
            //
            if (refill_last_o) begin
              for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
                tag_way_in[w2] = tag_way_save[w2];
                if (tag_save_lru[w2]) begin
                  tag_way_in[w2] = { 1'b1, curr_refill_adr[OPTION_DCACHE_LIMIT_WIDTH-1:WAY_WIDTH] };
                end
              end
              access_lru_history = tag_save_lru;
              tag_lru_in         = next_lru_history;
              // ---
              tag_we = 1'b1;
            end
          end // write & no exceptions & no pipe flushing
        end // re-fill

        DC_INVALIDATE: begin
          //
          // Lazy invalidation, invalidate everything that matches tag address
          //  # Pay attention we needn't to take into accaunt exceptions or
          //    pipe flusing here. It because, MARROCCHINO executes
          //    l.mf(t)spr commands after successfull completion of
          //    all previous instructions.
          //
          tag_windex = spr_bus_dat_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH]; // on invalidate
          tag_we     = 1'b1;
          tag_lru_in = 0;
          for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
            tag_way_in[w2] = 0;
          end
        end

        default: begin
        end
      endcase
    end
  end


  // RAM blocks read enable (WAYS & TAG common part)
  wire ram_re = (lsu_takes_load_i | lsu_takes_store_i) & enable_i & ~dc_force_idle;


  // Read / Write port (*_rwp_*) controls
  wire [OPTION_DCACHE_WAYS-1:0] way_rwp_we;
  // Write-only port (*_wp_*) controls
  wire [OPTION_DCACHE_WAYS-1:0] way_wp_en;

  // On re-fill we force using RW-port to provide correct read-hit
  // WAY-RAM read address
  wire [WAY_WIDTH-3:0] way_raddr = dc_refill ? curr_refill_adr[WAY_WIDTH-1:2] :
                                               virt_addr_i[WAY_WIDTH-1:2];
  // WAY-RAM write address
  //  # As way size is equal to page one we able to use ether
  //    physical or virtual indexing. We use virual indexing because
  //    it isn't changed by DMMU on/off.
  wire [WAY_WIDTH-3:0] way_waddr = dc_refill ? curr_refill_adr[WAY_WIDTH-1:2] :
                                               virt_addr_cmd_i[WAY_WIDTH-1:2];
  // support RW-conflict detection
  wire way_rw_same_addr = (way_raddr == way_waddr);

  generate
  for (i = 0; i < OPTION_DCACHE_WAYS; i=i+1) begin : way_memories
    // each way RAM read and write
    //  # on re-fill we force using RW-port to provide correct read-hit
    //  # pay attention that way-we already blocked by exceptions
    assign way_re[i] = ram_re | (way_we[i] & dc_refill);

    // Read / Write port (*_rwp_*) controls
    assign way_rwp_we[i] = way_we[i] & way_re[i] & way_rw_same_addr;

    // Write-only port (*_wp_*) controls
    assign way_wp_en[i]  = way_we[i] & (~way_re[i] | ~way_rw_same_addr);

    // WAY-RAM instances
    mor1kx_dpram_en_w1st_sclk
    #(
      .ADDR_WIDTH     (WAY_WIDTH-2),
      .DATA_WIDTH     (OPTION_OPERAND_WIDTH),
      .CLEAR_ON_INIT  (OPTION_DCACHE_CLEAR_ON_INIT)
    )
    dc_way_ram
    (
      // common clock
      .clk    (clk),
      // port "a": Read / Write (for RW-conflict case)
      .en_a   (way_re[i]),     // enable port "a"
      .we_a   (way_rwp_we[i]), // operation is "write"
      .addr_a (way_raddr),
      .din_a  (way_wr_dat),
      .dout_a (way_dout[i]),
      // port "b": Write if no RW-conflict
      .en_b   (way_wp_en[i]),  // enable port "b"
      .we_b   (way_we[i]),     // operation is "write"
      .addr_b (way_waddr),
      .din_b  (way_wr_dat),
      .dout_b ()            // not used
    );
  end

  if (OPTION_DCACHE_WAYS >= 2) begin : gen_u_lru
    mor1kx_cache_lru
    #(
      .NUMWAYS(OPTION_DCACHE_WAYS)
    )
    dc_lru
    (
      // Outputs
      .update      (next_lru_history),
      .lru_pre     (lru),
      .lru_post    (),
      // Inputs
      .current     (current_lru_history),
      .access      (access_lru_history)
    );
  end
  else begin // single way
    assign next_lru_history = current_lru_history;
  end
  endgenerate



  // TAG-RAM read address
  //  # Opposite to WAY-RAM case we don't force using RW-port
  //    on re-fill because  TAG either invalid or address miss
  assign tag_rindex = virt_addr_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH];

  // TAG-RAM same address for read and write
  wire tr_rw_same_addr = (tag_rindex == tag_windex);

  // Read/Write port (*_rwp_*) write
  wire tr_rwp_we = tag_we & ram_re & tr_rw_same_addr;

  // Write-only port (*_wp_*) enable
  wire tr_wp_en  = tag_we & (~ram_re | ~tr_rw_same_addr);

  // TAG-RAM instance
  mor1kx_dpram_en_w1st_sclk
  #(
    .ADDR_WIDTH     (OPTION_DCACHE_SET_WIDTH),
    .DATA_WIDTH     (TAGMEM_WIDTH),
    .CLEAR_ON_INIT  (OPTION_DCACHE_CLEAR_ON_INIT)
  )
  dc_tag_ram
  (
    // common clock
    .clk    (clk),
    // port "a": Read / Write (for RW-conflict case)
    .en_a   (ram_re),     // enable port "a"
    .we_a   (tr_rwp_we),  // operation is "write"
    .addr_a (tag_rindex),
    .din_a  (tag_din),
    .dout_a (tag_dout),
    // port "b": Write if no RW-conflict
    .en_b   (tr_wp_en),   // enable port "b"
    .we_b   (tag_we),     // operation is "write"
    .addr_b (tag_windex),
    .din_b  (tag_din),
    .dout_b ()            // not used
  );



  generate
  /* verilator lint_off WIDTH */
  if (OPTION_DCACHE_SNOOP != "NONE") begin : st_ram
  /* verilator lint_on WIDTH */
    // snoop RAM read & write
    //  # we force snoop invalidation through RW-port
    //    to provide snoop-hit off
    wire str_re = (snoop_event_i & ~snoop_check) | snoop_hit_o;
    wire str_we = dc_invalidate | snoop_hit_o;

    // address for Read/Write port
    //  # for soop-hit case tag-windex is equal to snoop-windex
    assign snoop_rindex = snoop_hit_o ? tag_windex : snoop_index;

    // same addresses for read and write
    wire str_rw_same_addr = (tag_windex == snoop_rindex);

    // Read / Write port (*_rwp_*) controls
    wire str_rwp_we = str_we & str_re & str_rw_same_addr;

    // Write-only port (*_wp_*) controls
    wire str_wp_en  = str_we & (~str_re | ~str_rw_same_addr);

    // TAG-RAM instance
    mor1kx_dpram_en_w1st_sclk
    #(
      .ADDR_WIDTH     (OPTION_DCACHE_SET_WIDTH),
      .DATA_WIDTH     (TAGMEM_WIDTH),
      .CLEAR_ON_INIT  (OPTION_DCACHE_CLEAR_ON_INIT)
    )
    dc_snoop_tag_ram
    (
      // clock
      .clk    (clk),
      // port "a": Read / Write (for RW-conflict case)
      .en_a   (str_re),       // enable port
      .we_a   (str_rwp_we),   // operation is "write"
      .addr_a (snoop_rindex),
      .din_a  (tag_din),
      .dout_a (snoop_dout),
      // port "b": Write if no RW-conflict
      .en_b   (str_wp_en),  // enable port "b"
      .we_b   (str_we),     // operation is "write"
      .addr_b (tag_windex),
      .din_b  (tag_din),
      .dout_b ()            // not used
    );
  end
  endgenerate

endmodule // mor1kx_dcache_marocchino
