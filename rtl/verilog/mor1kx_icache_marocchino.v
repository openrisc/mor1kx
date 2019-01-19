////////////////////////////////////////////////////////////////////////
//                                                                    //
//  mor1kx_icache_marocchino                                          //
//                                                                    //
//  Description: Instruction CACHE implementation                     //
//               The variant is tightly coupled with                  //
//               MAROCCHINO FETCH and IMMU                            //
//               (based on mor1kx_immu)                               //
//                                                                    //
////////////////////////////////////////////////////////////////////////
//                                                                    //
//   Copyright (C) 2012-2013 Stefan Kristiansson                      //
//                           stefan.kristiansson@saunalahti.fi        //
//                                                                    //
//                           Stefan Wallentowitz                      //
//                           stefan.wallentowitz@tum.de               //
//                                                                    //
//   Copyright (C) 2015-2018 Andrey Bacherov                          //
//                           avbacherov@opencores.org                 //
//                                                                    //
//      This Source Code Form is subject to the terms of the          //
//      Open Hardware Description License, v. 1.0. If a copy          //
//      of the OHDL was not distributed with this file, You           //
//      can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt       //
//                                                                    //
////////////////////////////////////////////////////////////////////////

`include "mor1kx-defines.v"

module mor1kx_icache_marocchino
#(
  parameter OPTION_OPERAND_WIDTH        = 32,
  parameter OPTION_ICACHE_BLOCK_WIDTH   =  5,
  parameter OPTION_ICACHE_SET_WIDTH     =  8,
  parameter OPTION_ICACHE_WAYS          =  2,
  parameter OPTION_ICACHE_LIMIT_WIDTH   = 32,
  parameter OPTION_ICACHE_CLEAR_ON_INIT =  0
)
(
  // clock and reset
  input                                 cpu_clk,
  input                                 cpu_rst,

  // pipe controls
  input                                 padv_s1_i,
  input                                 padv_s2_i,
  // fetch exceptions
  input                                 ibus_err_i,

  // configuration
  input                                 ic_enable_i,

  // regular requests in/out
  input      [OPTION_OPERAND_WIDTH-1:0] virt_addr_mux_i,
  input      [OPTION_OPERAND_WIDTH-1:0] virt_addr_s1o_i,
  input      [OPTION_OPERAND_WIDTH-1:0] virt_addr_s2o_i,
  input      [OPTION_OPERAND_WIDTH-1:0] phys_addr_s2t_i,
  input                                 immu_cache_inhibit_i,
  output                                ic_ack_o,
  output reg     [`OR1K_INSN_WIDTH-1:0] ic_dat_o,

  // IBUS access request
  output                                ibus_read_req_o,

  // re-fill
  output                                refill_req_o,
  input                                 to_refill_i,
  output reg                            ic_refill_first_o,
  input      [OPTION_OPERAND_WIDTH-1:0] phys_addr_s2o_i,
  input          [`OR1K_INSN_WIDTH-1:0] ibus_dat_i,
  input                                 ibus_burst_last_i,
  input                                 ibus_ack_i,

  // SPR interface
  input                          [15:0] spr_bus_addr_i,
  input                                 spr_bus_we_i,
  input                                 spr_bus_stb_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_i,
  output     [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o,
  output                                spr_bus_ack_o
);

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
  localparam TAGMEM_WAY_VALID = TAGMEM_WAY_WIDTH - 1;

  // Additionally, the tag memory entry contains an LRU value.
  // To avoid signal width [-1:0] for 1-way cache this generates
  // at least 1-bit LRU field.
  localparam TAG_LRU_WIDTH = (OPTION_ICACHE_WAYS > 1) ? (OPTION_ICACHE_WAYS*(OPTION_ICACHE_WAYS-1) >> 1) : 1;

  // Compute the total sum of the entry elements
  localparam TAGMEM_WIDTH = TAGMEM_WAY_WIDTH * OPTION_ICACHE_WAYS + TAG_LRU_WIDTH;

  // For convenience we define the position of the LRU in the tag
  // memory entries
  localparam TAG_LRU_MSB = TAGMEM_WIDTH - 1;
  localparam TAG_LRU_LSB = TAG_LRU_MSB - TAG_LRU_WIDTH + 1;


  // States
  localparam [3:0] IC_READ       = 4'b0001,
                   IC_REFILL     = 4'b0010,
                   IC_INVALIDATE = 4'b0100,
                   IC_SPR_ACK    = 4'b1000;
  // FSM state pointer
  reg [3:0] ic_state;
  // Particular state indicators
//wire   ic_read       = ic_state[0];
  wire   ic_refill     = ic_state[1];
  wire   ic_invalidate = ic_state[2];
  assign spr_bus_ack_o = ic_state[3];


  // The index we read and write from tag memory
  wire [OPTION_ICACHE_SET_WIDTH-1:0] tag_rindex;
  wire [OPTION_ICACHE_SET_WIDTH-1:0] tag_windex;

  // The data from the tag memory
  wire       [TAGMEM_WIDTH-1:0] tag_dout;
  wire   [TAGMEM_WAY_WIDTH-1:0] tag_dout_way [OPTION_ICACHE_WAYS-1:0];
  reg    [TAGMEM_WAY_WIDTH-1:0] tag_dout_way_s2o [OPTION_ICACHE_WAYS-1:0];

  // The data to the tag memory
  wire       [TAGMEM_WIDTH-1:0] tag_din;
  reg    [TAGMEM_WAY_WIDTH-1:0] tag_din_way [OPTION_ICACHE_WAYS-1:0];
  reg       [TAG_LRU_WIDTH-1:0] tag_din_lru;


  // Whether to write to the tag memory in this cycle
  reg                           tag_we;

  // outputs of way memories
  wire [OPTION_OPERAND_WIDTH-1:0] way_dout [OPTION_ICACHE_WAYS-1:0];

  // Does any way hit?
  wire                          hit;
  wire [OPTION_ICACHE_WAYS-1:0] hit_way;

  // This is the least recently used value before access the memory.
  // Those are one hot encoded.
  wire [OPTION_ICACHE_WAYS-1:0] lru_way;
  reg  [OPTION_ICACHE_WAYS-1:0] lru_way_refill_r; // register for re-fill process

  // The access vector to update the LRU history is the way that has
  // a hit or is refilled. It is also one-hot encoded.
  reg  [OPTION_ICACHE_WAYS-1:0] access_way_for_lru;
  reg  [OPTION_ICACHE_WAYS-1:0] access_way_for_lru_s2o; // register on IFETCH output
  // The current LRU history as read from tag memory.
  reg       [TAG_LRU_WIDTH-1:0] current_lru_history_s2o; // register on IFETCH output
  // The update value after we accessed it to write back to tag memory.
  wire      [TAG_LRU_WIDTH-1:0] next_lru_history;


  genvar i;


  //------------------//
  // Check parameters //
  //------------------//

  generate
  if (OPTION_ICACHE_LIMIT_WIDTH > OPTION_OPERAND_WIDTH) begin
    initial begin
      $display("ICACHE: OPTION_ICACHE_LIMIT_WIDTH > OPTION_OPERAND_WIDTH");
      $finish();
    end
  end
  endgenerate


  // detect per-way hit
  generate
  for (i = 0; i < OPTION_ICACHE_WAYS; i=i+1) begin : ways_out
    // WAY aliases of TAG-RAM output
    assign tag_dout_way[i] = tag_dout[(i+1)*TAGMEM_WAY_WIDTH-1:i*TAGMEM_WAY_WIDTH];
    // hit: compare stored tag with incoming tag and check valid bit
    assign hit_way[i] = tag_dout_way[i][TAGMEM_WAY_VALID] &
                        (tag_dout_way[i][TAG_WIDTH-1:0] ==
                         phys_addr_s2t_i[OPTION_ICACHE_LIMIT_WIDTH-1:WAY_WIDTH]);
  end
  endgenerate


  // read success
  assign hit = |hit_way;


  // Is the area cachable?
  wire   is_cacheble  = ic_enable_i & (~immu_cache_inhibit_i);
  // ICACHE ACK
  assign ic_ack_o     = is_cacheble &   hit;
  // RE-FILL request
  assign refill_req_o = is_cacheble & (~hit);

  // IBUS access request
  assign ibus_read_req_o = (~is_cacheble);


  // read result if success
  integer w0;
  always @ (*) begin
    ic_dat_o = {OPTION_OPERAND_WIDTH{1'b0}};
    // ---
    for (w0 = 0; w0 < OPTION_ICACHE_WAYS; w0=w0+1) begin : mux_dat_o
      if (hit_way[w0])
        ic_dat_o = way_dout[w0];
    end
  end // always


  //---------------//
  // SPR interface //
  //---------------//

  //  we don't expect R/W-collisions for SPRbus vs Write-Back cycles since
  //    SPRbus access start 1-clock later than Write-Back
  //    thanks to MT(F)SPR processing logic (see OMAN)

  // Registering SPR BUS incoming signals.

  // SPR BUS strobe registering
  reg                              spr_bus_stb_r;
  reg                              spr_bus_we_r;
  reg                       [14:0] spr_bus_addr_r;
  reg [(OPTION_OPERAND_WIDTH-1):0] spr_bus_dat_r;
  // ---
  always @(posedge cpu_clk) begin
    if (cpu_rst)
      spr_bus_stb_r <= 1'b0;
    else if (spr_bus_ack_o)
      spr_bus_stb_r <= 1'b0;
    else
      spr_bus_stb_r <= spr_bus_stb_i;
  end // at clock
  // ---
  always @(posedge cpu_clk) begin
    spr_bus_we_r   <= spr_bus_we_i;
    spr_bus_addr_r <= spr_bus_addr_i[14:0];
    spr_bus_dat_r  <= spr_bus_dat_i;
  end


  // ICACHE "chip select" / invalidation / data output
  wire spr_ic_cs  = spr_bus_stb_r & (spr_bus_addr_r[14:11] == `OR1K_SPR_IC_BASE);
  wire spr_ic_inv = spr_bus_we_r & (`SPR_OFFSET(spr_bus_addr_r) == `SPR_OFFSET(`OR1K_SPR_ICBIR_ADDR));
  assign spr_bus_dat_o = {OPTION_OPERAND_WIDTH{1'b0}};


  //-----------//
  // Cache FSM //
  //-----------//
  always @(posedge cpu_clk) begin
    if (cpu_rst) begin
      ic_refill_first_o <= 1'b0;    // reset
      ic_state          <= IC_READ; // reset
    end
    else begin
      // states
      // synthesis parallel_case
      case (ic_state)
        IC_READ: begin
          // to-re-fill or invalidate mean that neither
          // exceptions nor flushing has occured
          if (to_refill_i) begin            // FSM: read -> re-fill
            ic_refill_first_o <= 1'b1;      // FSM: read -> re-fill
            ic_state          <= IC_REFILL; // FSM: read -> re-fill
          end
          else if (spr_ic_cs) begin
            ic_state <= spr_ic_inv ? IC_INVALIDATE : IC_SPR_ACK; // FSM: read: SPR request processing
          end
        end // FSM-READ state

        IC_REFILL: begin
          // In according with WISHBONE-B3 rule 3.45:
          // "SLAVE MUST NOT assert more than one of ACK, ERR or RTY"
          if (ibus_err_i) begin           // FSM: during re-fill
            ic_refill_first_o <= 1'b0;    // FSM: IBUS error during re-fill
            ic_state          <= IC_READ; // FSM: IBUS error during re-fill
          end
          else if (ibus_ack_i) begin    // FSM: during re-fill
            ic_refill_first_o <= 1'b0;  // FSM: IBUS ack during re-fill
            if (ibus_burst_last_i)
              ic_state <= IC_READ;      // FSM: last re-fill
          end
        end // FRM-RE-FILL state

        IC_INVALIDATE: begin
          ic_state <= IC_SPR_ACK; // FSM: invalidate -> ack for SPR BUS
        end

        IC_SPR_ACK: begin
          ic_state <= IC_READ; // FSM: ack for SPR BUS -> idling
        end

        default:;
      endcase
    end // reset / regular update
  end // @ clock


  //   In fact we don't need different addresses per way
  // because we access WAY-RAM either for read or for re-fill, but
  // we don't do these simultaneously
  //   As way size is equal to page one we able to use either
  // physical or virtual indexing.

  // For re-fill we use local copy of bus-bridge's burst address
  //  accumulator to generate WAY-RAM index.
  // The approach increases logic locality and makes routing easier.
  reg  [OPTION_OPERAND_WIDTH-1:0] virt_addr_rfl_r;
  wire [OPTION_OPERAND_WIDTH-1:0] virt_addr_rfl_next;
  // cache block length is 5 -> burst length is 8: 32 bytes = (8 words x 32 bits/word)
  // cache block length is 4 -> burst length is 4: 16 bytes = (4 words x 32 bits/word)
  assign virt_addr_rfl_next = (OPTION_ICACHE_BLOCK_WIDTH == 5) ?
    {virt_addr_rfl_r[31:5], virt_addr_rfl_r[4:0] + 5'd4} : // 32 byte = (8 words x 32 bits/word)
    {virt_addr_rfl_r[31:4], virt_addr_rfl_r[3:0] + 4'd4};  // 16 byte = (4 words x 32 bits/word)
  // ---
  always @(posedge cpu_clk) begin
    // synthesis parallel_case
    case (ic_state)
      IC_READ: begin // re-fill address register
        if (spr_ic_cs)        // set re-fill address register to invaldate by l.mtspr
          virt_addr_rfl_r <= spr_bus_dat_r;   // invaldate by l.mtspr
        else if (padv_s2_i) // set re-fill address register to initial re-fill address
          virt_addr_rfl_r <= virt_addr_s1o_i; // prepare to re-fill (copy of LSU::s2o_virt_addr)
      end // check
      IC_REFILL: begin
        if (ibus_ack_i)
          virt_addr_rfl_r <= virt_addr_rfl_next;  // re-fill in progress
      end // re-fill
      default:;
    endcase
  end // @ clock

  // WAY WRITE INDEX
  wire [WAY_WIDTH-3:0] way_windex = virt_addr_rfl_r[WAY_WIDTH-1:2]; // makes sense at re-fill only

  // WAY READ INDEX
  wire [WAY_WIDTH-3:0] way_rindex = ic_refill ? virt_addr_s1o_i[WAY_WIDTH-1:2]: // WAY READ INDEX at re-fill
                                                virt_addr_mux_i[WAY_WIDTH-1:2]; // WAY READ INDEX at advance

  // Controls for read/write port.
  // We activate RW-port writting during re-fill only.
  wire [OPTION_ICACHE_WAYS-1:0] way_rwp_en;
  wire [OPTION_ICACHE_WAYS-1:0] way_rwp_we;
  // ---
  wire way_rwp_same_addr = (way_windex == virt_addr_s1o_i[WAY_WIDTH-1:2]);

  // Controls for write-only port
  wire [OPTION_ICACHE_WAYS-1:0] way_wp_we;
  // ---
  wire way_wp_diff_addr = (way_windex != virt_addr_s1o_i[WAY_WIDTH-1:2]);

  // WAY-RAM instances
  generate
  for (i = 0; i < OPTION_ICACHE_WAYS; i=i+1) begin : ways_ram
    // Controls for read/write port.
    // We activate RW-port during re-fill only.
    assign way_rwp_we[i] = ibus_ack_i & lru_way_refill_r[i] & way_rwp_same_addr;
    assign way_rwp_en[i] = padv_s1_i | way_rwp_we[i];

    // Controls for write-only port
    assign way_wp_we[i] = ibus_ack_i & lru_way_refill_r[i] & way_wp_diff_addr;

    // WAY-RAM instances
    mor1kx_dpram_en_w1st
    #(
      .ADDR_WIDTH     (WAY_WIDTH-2), // ICACHE_WAY_RAM
      .DATA_WIDTH     (OPTION_OPERAND_WIDTH), // ICACHE_WAY_RAM
      .CLEAR_ON_INIT  (OPTION_ICACHE_CLEAR_ON_INIT) // ICACHE_WAY_RAM
    )
    ic_way_ram
    (
      // port "a"
      .clk_a          (cpu_clk), // ICACHE_WAY_RAM
      .en_a           (way_rwp_en[i]), // ICACHE_WAY_RAM
      .we_a           (way_rwp_we[i]), // ICACHE_WAY_RAM
      .addr_a         (way_rindex), // ICACHE_WAY_RAM
      .din_a          (ibus_dat_i), // ICACHE_WAY_RAM
      .dout_a         (way_dout[i]), // ICACHE_WAY_RAM
      // port "b"
      .clk_b          (cpu_clk), // ICACHE_WAY_RAM
      .en_b           (way_wp_we[i]), // ICACHE_WAY_RAM
      .we_b           (1'b1), // ICACHE_WAY_RAM
      .addr_b         (way_windex), // ICACHE_WAY_RAM
      .din_b          (ibus_dat_i), // ICACHE_WAY_RAM
      .dout_b () // ICACHE_WAY_RAM
    );
  end // ways_ram
  endgenerate


  //--------------------//
  // TAG-RAM controller //
  //--------------------//

  // s2o_ic_ack, 1-clock length to prevent extra LRU updates
  reg s2o_ic_ack;
  // ---
  always @(posedge cpu_clk) begin
    if (cpu_rst)
      s2o_ic_ack <= 1'b0;
    else if (padv_s2_i)
      s2o_ic_ack <= ic_ack_o;
    else
      s2o_ic_ack <= 1'b0;
  end // @clock

  // LRU calculator
  generate
  /* verilator lint_off WIDTH */
  if (OPTION_ICACHE_WAYS >= 2) begin : gen_u_lru
  /* verilator lint_on WIDTH */
    mor1kx_cache_lru_marocchino
    #(
      .NUMWAYS(OPTION_ICACHE_WAYS) // ICACHE_LRU
    )
    ic_lru
    (
      // Inputs
      .current     (current_lru_history_s2o), // ICACHE_LRU
      .access      (access_way_for_lru), // ICACHE_LRU
      // Outputs
      .update      (next_lru_history), // ICACHE_LRU
      .lru_post    (lru_way) // ICACHE_LRU
    );
  end
  else begin // single way
    assign next_lru_history = 1'b1; // single way cache
    assign lru_way          = 1'b1; // single way cache
  end
  endgenerate

  // LRU related data registered on IFETCH output
  always @(posedge cpu_clk) begin
    if (padv_s2_i) begin
      access_way_for_lru_s2o  <= hit_way;
      current_lru_history_s2o <= tag_dout[TAG_LRU_MSB:TAG_LRU_LSB];
    end
  end // @clock

  // LRU way registered for re-fill process
  always @(posedge cpu_clk) begin
    if (to_refill_i) begin   // save lru way for re-fill
      lru_way_refill_r <= lru_way; // to re-fill
    end
    else if (ic_refill) begin
      if ((ibus_ack_i & ibus_burst_last_i) | ibus_err_i) begin
        lru_way_refill_r <= {OPTION_ICACHE_WAYS{1'b0}}; // last re-fill / IBUS error
      end
    end
    else
      lru_way_refill_r <= {OPTION_ICACHE_WAYS{1'b0}}; // default
  end // @clock

  // store tag state
  integer w1;
  always @(posedge cpu_clk) begin
    if (padv_s2_i) begin
      for (w1 = 0; w1 < OPTION_ICACHE_WAYS; w1 = w1 + 1) begin
        tag_dout_way_s2o[w1] <= tag_dout_way[w1];
      end
    end
  end // @clock

  // TAG-RAM "we" and data input
  integer w2;
  always @(*) begin
    // no write TAG-RAM by default
    tag_we = 1'b0; // by default

    // by default prepare data for LRU update at hit or for re-fill initiation
    //  -- input for LRU calculator
    access_way_for_lru  = access_way_for_lru_s2o; // by default
    //  -- output of LRU calculator
    tag_din_lru = next_lru_history; // by default
    //  -- other TAG-RAM fields
    for (w2 = 0; w2 < OPTION_ICACHE_WAYS; w2 = w2 + 1) begin
      tag_din_way[w2] = tag_dout_way_s2o[w2]; // by default
    end

    // synthesis parallel_case
    case (ic_state)
      IC_READ: begin
        // Update LRU data by read-hit only
        if (s2o_ic_ack) begin // on read-hit
          tag_we = 1'b1; // on read-hit
        end
      end

      IC_REFILL: begin
        if (ibus_err_i) begin
          //  (a) In according with WISHBONE-B3 rule 3.45:
          // "SLAVE MUST NOT assert more than one of ACK, ERR or RTY"
          //  (b) We don't interrupt re-fill on flushing, so the only reason
          // for invalidation is IBUS error occurence
          //  (c) Lazy invalidation, invalidate everything that matches tag address
          for (w2 = 0; w2 < OPTION_ICACHE_WAYS; w2 = w2 + 1) begin
            tag_din_way[w2] = {TAGMEM_WAY_WIDTH{1'b0}}; // IBUS error at re-fill
          end
          tag_din_lru = {TAG_LRU_WIDTH{1'b1}};  // by IBUS error at re-fill
          tag_we      = 1'b1;                   // by IBUS error at re-fill
        end
        else if (ibus_ack_i & ibus_burst_last_i) begin
          // After refill update the tag memory entry of the
          // filled way with the LRU history, the tag and set
          // valid to 1.
          for (w2 = 0; w2 < OPTION_ICACHE_WAYS; w2 = w2 + 1) begin
            if (lru_way_refill_r[w2]) begin // last re-fill
              tag_din_way[w2] = {1'b1,phys_addr_s2o_i[OPTION_ICACHE_LIMIT_WIDTH-1:WAY_WIDTH]}; // last re-fill
            end
          end
          access_way_for_lru = lru_way_refill_r;  // last re-fill
          tag_we             = 1'b1;              // last re-fill
        end
      end

      IC_INVALIDATE: begin
        // Lazy invalidation, invalidate everything that matches tag address
        for (w2 = 0; w2 < OPTION_ICACHE_WAYS; w2 = w2 + 1) begin
          tag_din_way[w2] = {TAGMEM_WAY_WIDTH{1'b0}}; // by invalidate
        end
        tag_din_lru = {TAG_LRU_WIDTH{1'b1}};  // by invalidate
        tag_we      = 1'b1;                   // by invalidate
      end

      default:;
    endcase
  end // always


  // Pack TAG-RAM data input
  //  # LRU section
  assign tag_din[TAG_LRU_MSB:TAG_LRU_LSB] = tag_din_lru;
  //  # WAY sections collection
  generate
  for (i = 0; i < OPTION_ICACHE_WAYS; i=i+1) begin : tw_sections
    assign tag_din[(i+1)*TAGMEM_WAY_WIDTH-1:i*TAGMEM_WAY_WIDTH] = tag_din_way[i];
  end
  endgenerate

  /*
   * The tag mem is written during:
   *  - last refill
   *  - invalidate
   *  - update LRU info
   *
   *   As way size is equal to page one we able to use either
   * physical or virtual indexing.
   */
  assign tag_windex = virt_addr_rfl_r[WAY_WIDTH-1:OPTION_ICACHE_BLOCK_WIDTH]; // TAG_WR_ADDR at invalidate / re-fill / update LRU

  // TAG read address
  assign tag_rindex = padv_s1_i ? virt_addr_mux_i[WAY_WIDTH-1:OPTION_ICACHE_BLOCK_WIDTH] : // TAG_RE_ADDR at regular advance
                                  virt_addr_s1o_i[WAY_WIDTH-1:OPTION_ICACHE_BLOCK_WIDTH];  // TAG_RE_ADDR at re-fill, invalidate

  // Read/Write port (*_rwp_*) write
  wire tag_rwp_we = tag_we & (tag_rindex == tag_windex);
  wire tag_rwp_en = padv_s1_i | tag_rwp_we;

  // Write-only port (*_wp_*) enable
  wire tag_wp_en = tag_we & (tag_rindex != tag_windex);

  //------------------//
  // TAG-RAM instance //
  //------------------//

  mor1kx_dpram_en_w1st
  #(
    .ADDR_WIDTH     (OPTION_ICACHE_SET_WIDTH), // ICACHE_TAG_RAM
    .DATA_WIDTH     (TAGMEM_WIDTH), // ICACHE_TAG_RAM
    .CLEAR_ON_INIT  (OPTION_ICACHE_CLEAR_ON_INIT) // ICACHE_TAG_RAM
  )
  ic_tag_ram
  (
    // port "a": Read / Write (for RW-conflict case)
    .clk_a  (cpu_clk), // ICACHE_TAG_RAM
    .en_a   (tag_rwp_en), // ICACHE_TAG_RAM
    .we_a   (tag_rwp_we), // ICACHE_TAG_RAM
    .addr_a (tag_rindex), // ICACHE_TAG_RAM
    .din_a  (tag_din), // ICACHE_TAG_RAM
    .dout_a (tag_dout), // ICACHE_TAG_RAM
    // port "b": Write if no RW-conflict
    .clk_b  (cpu_clk), // ICACHE_TAG_RAM
    .en_b   (tag_wp_en), // ICACHE_TAG_RAM
    .we_b   (1'b1), // ICACHE_TAG_RAM
    .addr_b (tag_windex), // ICACHE_TAG_RAM
    .din_b  (tag_din), // ICACHE_TAG_RAM
    .dout_b () // ICACHE_TAG_RAM
  );

endmodule // mor1kx_icache_marocchino
