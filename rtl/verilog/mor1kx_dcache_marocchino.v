////////////////////////////////////////////////////////////////////////
//                                                                    //
//  mor1kx_dcache_marocchino                                          //
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
  input                                 cpu_clk,
  input                                 cpu_rst,

  // pipe controls
  input                                 lsu_s1_adv_i,
  input                                 lsu_s2_adv_i,
  input                                 pipeline_flush_i,

  // configuration
  input                                 dc_enable_i,

  // exceptions
  input                                 s2o_excepts_addr_i,
  input                                 dbus_err_i,

  // Regular operation
  //  # addresses and "DCHACHE inhibit" flag
  input      [OPTION_OPERAND_WIDTH-1:0] virt_addr_idx_i,
  input      [OPTION_OPERAND_WIDTH-1:0] virt_addr_s1o_i,
  input      [OPTION_OPERAND_WIDTH-1:0] virt_addr_s2o_i,
  input      [OPTION_OPERAND_WIDTH-1:0] phys_addr_s2t_i,
  input                                 dmmu_cache_inhibit_i,
  //  # DCACHE regular answer
  input                                 s1o_op_lsu_load_i,
  output                                dc_ack_read_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] dc_dat_o,
  //  # STORE format / store data / do storing
  input                                 s1o_op_lsu_store_i,
  input                           [3:0] dbus_bsel_i,
  input      [OPTION_OPERAND_WIDTH-1:0] dbus_sdat_i,
  input      [OPTION_OPERAND_WIDTH-1:0] dc_dat_s2o_i,
  input                                 dc_store_allowed_i,
  // !!! (mor1kx_lsu_marocchino.dc_store_cancel == dc_cancel) !!!
  //input                                 dc_store_cancel_i,
  //  # Atomics
  input                                 s1o_op_lsu_atomic_i,

  // re-fill
  output                                dc_refill_req_o,
  input                                 dc_refill_allowed_i,
  output reg                            refill_first_o,
  input      [OPTION_OPERAND_WIDTH-1:0] phys_addr_s2o_i,
  input      [OPTION_OPERAND_WIDTH-1:0] dbus_dat_i,
  input                                 dbus_burst_last_i,
  input                                 dbus_ack_i,

  // DBUS read request
  output                                dbus_read_req_o,

  // SNOOP
  input      [OPTION_OPERAND_WIDTH-1:0] snoop_adr_i,
  input                                 snoop_en_i,
  output                                s2o_snoop_proc_o,
  input                                 dc_snoop2refill_i,
  input                                 dc_snoop2write_i,

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

  // Additionally, the tag memory entry contains an LRU value.
  // To avoid signal width [-1:0] for 1-way cache this generates
  // at least 1-bit LRU field.
  localparam TAG_LRU_WIDTH = (OPTION_DCACHE_WAYS > 1) ? (OPTION_DCACHE_WAYS*(OPTION_DCACHE_WAYS-1)>>1) : 1;

  // Compute the total sum of the entry elements
  localparam TAGMEM_WIDTH = TAGMEM_WAY_WIDTH * OPTION_DCACHE_WAYS + TAG_LRU_WIDTH;

  // For convenience we define the position of the LRU in the tag
  // memory entries
  localparam TAG_LRU_MSB = TAGMEM_WIDTH - 1;
  localparam TAG_LRU_LSB = TAG_LRU_MSB - TAG_LRU_WIDTH + 1;


  // States
  localparam  [7:0] DC_CHECK         = 8'b00000001,
                    DC_WRITE         = 8'b00000010,
                    DC_REFILL        = 8'b00000100,
                    DC_INV_BY_MTSPR  = 8'b00001000,
                    DC_INV_BY_ATOMIC = 8'b00010000,
                    DC_INV_BY_SNOOP  = 8'b00100000,
                    DC_SPR_ACK       = 8'b01000000,
                    DC_RST           = 8'b10000000;

  // FSM state register
  reg [7:0] dc_state;
  // FSM state signals
  wire   dc_check         = dc_state[0];
  wire   dc_write         = dc_state[1];
  wire   dc_refill        = dc_state[2];
  wire   dc_inv_by_mtspr  = dc_state[3];
  wire   dc_inv_by_atomic = dc_state[4];
  wire   dc_inv_by_snoop  = dc_state[5];


  // The index we read and write from tag memory
  wire [OPTION_DCACHE_SET_WIDTH-1:0] tag_rindex;
  wire [OPTION_DCACHE_SET_WIDTH-1:0] tag_windex;

  // The data from the tag memory
  wire       [TAGMEM_WIDTH-1:0] tag_dout;
  wire   [TAGMEM_WAY_WIDTH-1:0] tag_dout_way [OPTION_DCACHE_WAYS-1:0];
  reg    [TAGMEM_WAY_WIDTH-1:0] tag_dout_way_s2o [OPTION_DCACHE_WAYS-1:0];

  // The data to the tag memory
  wire      [TAGMEM_WIDTH-1:0] tag_din;
  reg   [TAGMEM_WAY_WIDTH-1:0] tag_din_way [OPTION_DCACHE_WAYS-1:0];
  reg      [TAG_LRU_WIDTH-1:0] tag_din_lru;


  // Whether to write to the tag memory in this cycle
  reg                          tag_we;



  // WAYs related
  reg    [OPTION_DCACHE_WAYS-1:0] way_we; // Write signals per way
  reg  [OPTION_OPERAND_WIDTH-1:0] way_din;
  wire            [WAY_WIDTH-3:0] way_windex;
  wire            [WAY_WIDTH-3:0] way_rindex;
  wire [OPTION_OPERAND_WIDTH-1:0] way_dout [OPTION_DCACHE_WAYS-1:0];


  // Does any way hit?
  wire                          dc_hit;
  wire [OPTION_DCACHE_WAYS-1:0] dc_hit_way;
  reg  [OPTION_DCACHE_WAYS-1:0] s2o_hit_way; // latched in stage #2 register

  // This is the least recently used value before access the memory.
  // Those are one hot encoded.
  wire [OPTION_DCACHE_WAYS-1:0] lru_way;
  reg  [OPTION_DCACHE_WAYS-1:0] lru_way_refill_r; // for re-fill

  // The current LRU history as read from tag memory.
  reg       [TAG_LRU_WIDTH-1:0] lru_history_curr_s2o; // registered
  reg  [OPTION_DCACHE_WAYS-1:0] access_way_for_lru; // for update LRU history
  // The update value after we accessed it to write back to tag memory.
  wire      [TAG_LRU_WIDTH-1:0] lru_history_next;



  // Snoop-Invalidation interface to TAG-RAM
  // Snoop-Hit flag (1-clok length)
  wire s2o_snoop_hit;
  // Each ways information in the tag memory
  wire   [TAGMEM_WAY_WIDTH-1:0] inv_snoop_dout_way [OPTION_DCACHE_WAYS-1:0];
  // Whether the way hits
  wire [OPTION_DCACHE_WAYS-1:0] inv_snoop_hit_way;
  // Indexing TAG-RAM and SNOOP-TAG-RAM during invalidation
  wire [OPTION_OPERAND_WIDTH-1:0] s2o_snoop_adr;
  // Drop write-hit if it is snooped
  wire inv_snoop_dc_ack_write;


  genvar i;


  //------------------//
  // Check parameters //
  //------------------//

  generate
  if (OPTION_DCACHE_LIMIT_WIDTH > OPTION_OPERAND_WIDTH) begin
    initial begin
      $display("DCACHE: OPTION_DCACHE_LIMIT_WIDTH > OPTION_OPERAND_WIDTH");
      $finish();
    end
  end
  endgenerate


  // detect per-way hit
  generate
  for (i = 0; i < OPTION_DCACHE_WAYS; i = i + 1) begin : gen_per_way_hit
    // Unpack per-way tags
    assign tag_dout_way[i] = tag_dout[(i+1)*TAGMEM_WAY_WIDTH-1:i*TAGMEM_WAY_WIDTH];
    // compare stored tag with incoming tag and check valid bit
    assign dc_hit_way[i] = tag_dout_way[i][TAGMEM_WAY_VALID] &
                           (tag_dout_way[i][TAG_WIDTH-1:0] ==
                            phys_addr_s2t_i[OPTION_DCACHE_LIMIT_WIDTH-1:WAY_WIDTH]); // hit detection
  end
  endgenerate

  // overall hit
  assign dc_hit = |dc_hit_way;


  // Is the area cachable?
  wire   is_cacheble     = dc_enable_i & (~dmmu_cache_inhibit_i);

  // for write processing
  wire   dc_ack_write    = s1o_op_lsu_store_i & (~s1o_op_lsu_atomic_i) & is_cacheble &   dc_hit;
  reg    s2o_dc_ack_write;

  // if requested data were fetched before snoop-hit, it is valid
  assign dc_ack_read_o   = s1o_op_lsu_load_i  & (~s1o_op_lsu_atomic_i) & is_cacheble &   dc_hit;
  reg    s2o_dc_ack_read;

  // re-fill reqest
  assign dc_refill_req_o = s1o_op_lsu_load_i  & (~s1o_op_lsu_atomic_i) & is_cacheble & (~dc_hit);

  // DBUS access request
  assign dbus_read_req_o = s1o_op_lsu_load_i  & (s1o_op_lsu_atomic_i | (~is_cacheble));


  // read result if success
  integer w0;
  always @ (*) begin
    dc_dat_o = {OPTION_OPERAND_WIDTH{1'b0}};
    // ---
    for (w0 = 0; w0 < OPTION_DCACHE_WAYS; w0=w0+1) begin : mux_dat_o
      if (dc_hit_way[w0])
        dc_dat_o = way_dout[w0];
    end
  end // always



  /*
   * SPR bus interface
   *  # Only invalidate command is implemented
   *  # In MAROCCHINO pipeline l.mf(t)spr instructions are executed
   *    if pipeline is stalled.
   */

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

  // DCACHE "chip select" / invalidation / data output
  wire spr_dc_cs  = spr_bus_stb_r & (spr_bus_addr_r[14:11] == `OR1K_SPR_DC_BASE);
  wire spr_dc_inv = spr_bus_we_r & ((`SPR_OFFSET(spr_bus_addr_r) == `SPR_OFFSET(`OR1K_SPR_DCBFR_ADDR)) |
                                    (`SPR_OFFSET(spr_bus_addr_r) == `SPR_OFFSET(`OR1K_SPR_DCBIR_ADDR)));
  assign spr_bus_dat_o = {OPTION_OPERAND_WIDTH{1'b0}};



  /*
   * DCACHE FSM controls
   */

  // Cancel operation by pipe flusing or an address related exception
  // !!! (mor1kx_lsu_marocchino.dc_store_cancel == dc_cancel) !!!
  wire dc_cancel = s2o_excepts_addr_i | pipeline_flush_i;


  /*
   * DCACHE FSM
   */

  // DCACHE FSM: state switching
  always @(posedge cpu_clk) begin
    if (cpu_rst) begin
      dc_state      <= DC_RST; // on reset
      spr_bus_ack_o <= 1'b0; // on reset
    end
    else begin
      // synthesis parallel_case
      case (dc_state)
        DC_CHECK: begin
          if (s2o_snoop_hit) begin // check -> snoop-inv
            dc_state <= DC_INV_BY_SNOOP; // check -> snoop-inv
          end
          else if (dc_refill_allowed_i) begin // check -> re-fill
            dc_state <= DC_REFILL; // check -> re-fill
          end
          else if (dc_cancel) begin // keep check
            dc_state <= DC_CHECK;
          end
          else if (spr_dc_cs) begin // check -> invalidate by l.mtspr
            dc_state <= spr_dc_inv ? DC_INV_BY_MTSPR : DC_SPR_ACK; // check: SPR request processing
          end
          else if (lsu_s2_adv_i) begin // check -> write / keep check
            dc_state <= s1o_op_lsu_atomic_i ? DC_INV_BY_ATOMIC :      // check -> invalidate by lwa/swa
                          (s1o_op_lsu_store_i ? DC_WRITE : DC_CHECK); // check -> write / keep check
          end
        end // check

        DC_WRITE: begin
          // (1) stage #2 advance is impossible till either
          //     write completion or DBUS error (for l.swa)
          // (2) !!! (mor1kx_lsu_marocchino.dc_store_cancel == dc_cancel) !!!
          if (s2o_snoop_hit) // write -> snoop-inv
            dc_state <= DC_INV_BY_SNOOP; // write -> snoop-inv
          else if (dc_store_allowed_i | dc_cancel) // done / abort dc-write
            dc_state <= DC_CHECK; // done / abort write
        end // write

        DC_REFILL: begin
          // In according with WISHBONE-B3 rule 3.45:
          //  "SLAVE MUST NOT assert more than one of ACK, ERR or RTY"
          if (s2o_snoop_hit) // re-fill -> snoop-inv
            dc_state <= DC_INV_BY_SNOOP; // re-fill -> snoop-inv
          else if (dbus_err_i | (dbus_ack_i & dbus_burst_last_i)) // abort / done re-fill
            dc_state <= DC_CHECK;        // abort / done re-fill
        end // re-fill

        DC_INV_BY_MTSPR: begin
          // next state
          dc_state <= (s2o_snoop_hit ? DC_INV_BY_SNOOP : DC_SPR_ACK); // invalidate by l.mtspr
          // rize SPR BUS ACK any case
          spr_bus_ack_o <= 1'b1; // invalidate by l.mtspr
        end

        DC_INV_BY_ATOMIC: begin
          dc_state <= (s2o_snoop_hit ? DC_INV_BY_SNOOP : DC_CHECK); // invalidate by lwa/swa
        end

        DC_INV_BY_SNOOP: begin
          // !!! (mor1kx_lsu_marocchino.dc_store_cancel == dc_cancel) !!!
          if (~s2o_snoop_hit) begin // snoop-inv -> back
            dc_state <= dc_snoop2refill_i ? DC_REFILL : // snoop-inv -> re-fill
                          ((dc_snoop2write_i & (~dc_cancel)) ? DC_WRITE : // snoop-inv -> write
                                                               DC_CHECK); // snoop-inv -> check
          end
          // force drop SPR BUS ACK
          spr_bus_ack_o <= 1'b0; // snoop-inv
        end

        DC_SPR_ACK: begin
          // next state
          dc_state <= (s2o_snoop_hit ? DC_INV_BY_SNOOP : DC_CHECK); // l.mtspr ack
          // drop SPR BUS ACK
          spr_bus_ack_o <= 1'b0; // l.mtspr ack
        end

        DC_RST: begin
          dc_state <= DC_CHECK; // on doing reset
        end

        default:;
      endcase
    end
  end // at clock

  //
  // DCACHE FSM: various data
  //
  always @(posedge cpu_clk) begin
    // states switching
    // synthesis parallel_case
    case (dc_state)
      DC_CHECK: begin
        // next states
        if (s2o_snoop_hit) begin
        end
        else if (dc_refill_allowed_i) begin
          lru_way_refill_r <= lru_way;    // check -> re-fill
          refill_first_o   <= 1'b1;       // check -> re-fill
        end
        else if (dc_cancel) begin // keep check
        end
        else if (lsu_s2_adv_i) begin // check -> write / keep check
          s2o_dc_ack_write <= dc_ack_write; // check -> write / keep check
        end
      end // check

      DC_WRITE: begin
        // !!! (mor1kx_lsu_marocchino.dc_store_cancel == dc_cancel) !!!
        if (dc_store_allowed_i | dc_cancel) // done / abort dc-write
          s2o_dc_ack_write <= 1'b0;     // done / abort dc-write
      end // write

      DC_REFILL: begin
        // In according with WISHBONE-B3 rule 3.45:
        //   "SLAVE MUST NOT assert more than one of ACK, ERR or RTY"
        if (dbus_err_i) begin  // abort re-fill
          refill_first_o   <= 1'b0; // on dbus error during re-fill
          lru_way_refill_r <= {OPTION_DCACHE_WAYS{1'b0}};  // on dbus error during re-fill
        end
        else if (dbus_ack_i) begin
          refill_first_o <= 1'b0; // any re-fill
          if (dbus_burst_last_i) begin
            lru_way_refill_r <= {OPTION_DCACHE_WAYS{1'b0}}; // on last re-fill
          end
        end // snoop-hit / dbus-ack
      end // re-fill

      DC_INV_BY_SNOOP: begin
        // drop write hit if write position is snooped
        if (inv_snoop_dc_ack_write)
          s2o_dc_ack_write <= 1'b0; // snoop hit at same address
        // restore state after snoop hit processing
        if (~s2o_snoop_hit) begin // data
          if (dc_snoop2refill_i) begin
            lru_way_refill_r <= lru_way; // snoop-inv -> re-fill
            refill_first_o   <= 1'b1;    // snoop-inv -> re-fill
          end
        end
      end

      DC_RST: begin
        refill_first_o   <= 1'b0; // on reset
        lru_way_refill_r <= {OPTION_DCACHE_WAYS{1'b0}}; // on reset
        s2o_dc_ack_write <= 1'b0; // on reset
      end

      default:;
    endcase
  end // @ clock

  //
  // For re-fill we use local copy of bus-bridge's burst address
  //  accumulator to generate WAY-RAM index.
  // The approach increases logic locality and makes routing easier.
  //
  reg  [OPTION_OPERAND_WIDTH-1:0] virt_addr_rfl_r;
  wire [OPTION_OPERAND_WIDTH-1:0] virt_addr_rfl_next;
  // cache block length is 5 -> burst length is 8: 32 bytes = (8 words x 32 bits/word)
  // cache block length is 4 -> burst length is 4: 16 bytes = (4 words x 32 bits/word)
  assign virt_addr_rfl_next = (OPTION_DCACHE_BLOCK_WIDTH == 5) ?
    {virt_addr_rfl_r[31:5], virt_addr_rfl_r[4:0] + 5'd4} : // 32 byte = (8 words x 32 bits/word)
    {virt_addr_rfl_r[31:4], virt_addr_rfl_r[3:0] + 4'd4};  // 16 byte = (4 words x 32 bits/word)
  // ---
  always @(posedge cpu_clk) begin
    // synthesis parallel_case
    case (dc_state)
      DC_CHECK: begin // re-fill address register
        if (s2o_snoop_hit)      // set re-fill address register to invaldate by snoop-hit
          virt_addr_rfl_r <= s2o_snoop_adr;   // invaldate by snoop-hit
        else if (spr_dc_cs)     // set re-fill address register to invaldate by l.mtspr
          virt_addr_rfl_r <= spr_bus_dat_r;   // invaldate by l.mtspr
        else if (lsu_s2_adv_i)  // set re-fill address register to initial re-fill address
          virt_addr_rfl_r <= virt_addr_s1o_i; // prepare to re-fill (copy of LSU::s2o_virt_addr)
      end // check

      DC_REFILL: begin
        if (dbus_ack_i)
          virt_addr_rfl_r <= virt_addr_rfl_next;  // re-fill in progress
      end // re-fill

      DC_INV_BY_SNOOP: begin
        if (s2o_snoop_hit)
          virt_addr_rfl_r <= s2o_snoop_adr; // continue snoop-inv
        else
          virt_addr_rfl_r <= virt_addr_s2o_i; // snoop-inv -> back
      end // snoop-inv

      default:;
    endcase
  end // @ clock


  // s2o_* latches for WAY-fields of TAG
  integer w1;
  // ---
  always @(posedge cpu_clk) begin
    if (lsu_s2_adv_i) begin
      for (w1 = 0; w1 < OPTION_DCACHE_WAYS; w1 = w1 + 1) begin
        tag_dout_way_s2o[w1] <= tag_dout_way[w1];
      end
    end
  end // @clock

  // s2o_* latch for hit and current LRU history
  always @(posedge cpu_clk) begin
    if (lsu_s2_adv_i) begin
      s2o_hit_way          <= dc_hit_way;
      lru_history_curr_s2o <= tag_dout[TAG_LRU_MSB:TAG_LRU_LSB];
    end
  end // @clock


  // Local copy of LSU's s2o_dc_ack_read, but 1-clock length
  always @(posedge cpu_clk) begin
    if (cpu_rst)
      s2o_dc_ack_read <= 1'b0;
    else if (lsu_s2_adv_i)
      s2o_dc_ack_read <= dc_ack_read_o;
    else
      s2o_dc_ack_read <= 1'b0;
  end // @clock


  //
  // This is the combinational part of the state machine
  // that interfaces the tag and way memories.
  //


  integer w2;
  always @(*) begin
    // default prepare data for LRU update at hit or for re-fill initiation
    //  -- input for LRU calculator
    access_way_for_lru = s2o_hit_way; // default
    //  -- output of LRU calculator
    tag_din_lru = lru_history_next; // default
    //  -- other TAG-RAM fields
    for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
      tag_din_way[w2] = tag_dout_way_s2o[w2]; // default
    end

    //   As way size is equal to page one we able to use either
    // physical or virtual indexing.

    // TAG-RAM
    tag_we  = 1'b0; // default

    // WAYS-RAM
    way_we  = {OPTION_DCACHE_WAYS{1'b0}}; // default
    way_din = dbus_dat_i; // default as for re-fill

    // synthesis parallel_case
    case (dc_state)
      DC_CHECK: begin
        if (s2o_dc_ack_read & (~s2o_excepts_addr_i)) begin // on read-hit
          tag_we = 1'b1; // on read-hit
        end
      end

      DC_WRITE: begin
        // prepare data for write ahead
        way_din[31:24] = dbus_bsel_i[3] ? dbus_sdat_i[31:24] : dc_dat_s2o_i[31:24]; // on write-hit
        way_din[23:16] = dbus_bsel_i[2] ? dbus_sdat_i[23:16] : dc_dat_s2o_i[23:16]; // on write-hit
        way_din[15:8]  = dbus_bsel_i[1] ? dbus_sdat_i[15: 8] : dc_dat_s2o_i[15: 8]; // on write-hit
        way_din[7:0]   = dbus_bsel_i[0] ? dbus_sdat_i[ 7: 0] : dc_dat_s2o_i[ 7: 0]; // on write-hit
        // real update on write-hit only
        // !!! (mor1kx_lsu_marocchino.dc_store_cancel == dc_cancel) !!!
        if (s2o_dc_ack_write & dc_store_allowed_i & (~dc_cancel)) begin // on write-hit
          way_we = s2o_hit_way; // on write-hit
          tag_we = 1'b1;        // on write-hit
        end
      end

      DC_REFILL: begin
        // TAGs
        //  (a) In according with WISHBONE-B3 rule 3.45:
        // "SLAVE MUST NOT assert more than one of ACK, ERR or RTY"
        //  (b) We don't interrupt re-fill on flushing, so the only reason
        // for invalidation is DBUS error occurence
        //  (c) Lazy invalidation, invalidate everything that matches tag address
        if (dbus_err_i) begin // during re-fill
          for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
            tag_din_way[w2] = {TAGMEM_WAY_WIDTH{1'b0}}; // DBUS error  during re-fill
          end
          tag_din_lru = {TAG_LRU_WIDTH{1'b1}}; // invalidate by DBUS error at re-fill
          tag_we      = 1'b1; // invalidate by DBUS error during re-fill
        end
        else if (dbus_ack_i) begin
          // LRU WAY content update each DBUS ACK
          way_we = lru_way_refill_r; // on re-fill: write the data to the way that is replaced (which is the LRU)
          // After re-fill update the tag memory entry of the
          // filled way with the LRU history, the tag and set
          // valid to 1.
          if (dbus_burst_last_i) begin
            for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
              if (lru_way_refill_r[w2])
                tag_din_way[w2] = {1'b1, phys_addr_s2o_i[OPTION_DCACHE_LIMIT_WIDTH-1:WAY_WIDTH]};
            end
            access_way_for_lru = lru_way_refill_r;  // last re-fill
            tag_we             = 1'b1;              // last re-fill
          end
        end
      end // re-fill

      DC_INV_BY_MTSPR: begin
        //
        // Lazy invalidation, invalidate everything that matches tag address
        //  # Pay attention we needn't to take into accaunt exceptions or
        //    pipe flusing here. It because, MARROCCHINO executes
        //    l.mf(t)spr commands after successfull completion of
        //    all previous instructions.
        //
        for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
          tag_din_way[w2] = {TAGMEM_WAY_WIDTH{1'b0}};  // on invalidate by l.mtspr
        end
        tag_din_lru = {TAG_LRU_WIDTH{1'b1}}; // on invalidate by l.mtspr
        tag_we      = 1'b1;                  // on invalidate by l.mtspr
      end

      DC_INV_BY_ATOMIC: begin
        //
        // With the simplest approach we just force linked
        // address to be not cachable.
        // The address is also declared as freshest by LRU calculator
        // that delays re-filling of it.
        // MAROCCHINO_TODO: more accurate processing if linked address is cachable.
        //
        for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
          if (s2o_hit_way[w2])                          // on invalidate by lwa/swa
            tag_din_way[w2] = {TAGMEM_WAY_WIDTH{1'b0}}; // on invalidate by lwa/swa
        end
        tag_we = 1'b1;                                  // on invalidate by lwa/swa
      end

      DC_INV_BY_SNOOP: begin
        // MAROCCHINO_TODO: it would be better to set the way as LRU.
        for (w2 = 0; w2 < OPTION_DCACHE_WAYS; w2 = w2 + 1) begin
          tag_din_way[w2] = inv_snoop_hit_way[w2] ? {TAGMEM_WAY_WIDTH{1'b0}} : inv_snoop_dout_way[w2]; // on snoop-hit
        end
        access_way_for_lru = {OPTION_DCACHE_WAYS{1'b0}}; // on snoop-hit (keep history)
        tag_we             = 1'b1;                       // on snoop-hit
      end

      default:;
    endcase
  end


  // WAY WRITE INDEX
  assign way_windex = virt_addr_rfl_r[WAY_WIDTH-1:2];  // WAY WRITE INDEX for re-fill / write-hit

  // WAY_RE_ADDR
  assign way_rindex = lsu_s1_adv_i ?
                        virt_addr_idx_i[WAY_WIDTH-1:2] : // WAY_RE_ADDR if advance stage #1
                        virt_addr_s1o_i[WAY_WIDTH-1:2];  // WAY_RE_ADDR at re-fill / write-hit

  // Controls for read/write port.
  wire [OPTION_DCACHE_WAYS-1:0] way_rwp_en;
  wire [OPTION_DCACHE_WAYS-1:0] way_rwp_we;
  // ---
  wire way_rwp_same_addr = (way_windex == way_rindex);

  // Controls for write-only port
  wire [OPTION_DCACHE_WAYS-1:0] way_wp_we;
  // ---
  wire way_wp_diff_addr = (way_windex != way_rindex);

  // WAY-RAM Blocks
  generate
  for (i = 0; i < OPTION_DCACHE_WAYS; i=i+1) begin : way_memories
    // Controls for read/write port.
    assign way_rwp_we[i] = way_we[i] & way_rwp_same_addr;
    assign way_rwp_en[i] = lsu_s1_adv_i | way_rwp_we[i];

    // Controls for write-only port
    assign way_wp_we[i] = way_we[i] & way_wp_diff_addr;

    // WAY-RAM instances
    mor1kx_dpram_en_w1st
    #(
      .ADDR_WIDTH     (WAY_WIDTH-2), // DCACHE_WAY_RAM
      .DATA_WIDTH     (OPTION_OPERAND_WIDTH), // DCACHE_WAY_RAM
      .CLEAR_ON_INIT  (OPTION_DCACHE_CLEAR_ON_INIT) // DCACHE_WAY_RAM
    )
    dc_way_ram
    (
      // port "a"
      .clk_a          (cpu_clk), // DCACHE_WAY_RAM
      .en_a           (way_rwp_en[i]), // DCACHE_WAY_RAM
      .we_a           (way_rwp_we[i]), // DCACHE_WAY_RAM
      .addr_a         (way_rindex), // DCACHE_WAY_RAM
      .din_a          (way_din), // DCACHE_WAY_RAM
      .dout_a         (way_dout[i]), // DCACHE_WAY_RAM
      // port "b"
      .clk_b          (cpu_clk), // DCACHE_WAY_RAM
      .en_b           (way_wp_we[i]), // DCACHE_WAY_RAM
      .we_b           (1'b1), // DCACHE_WAY_RAM
      .addr_b         (way_windex), // DCACHE_WAY_RAM
      .din_b          (way_din), // DCACHE_WAY_RAM
      .dout_b         () // DCACHE_WAY_RAM
    );
  end
  endgenerate


  // LRU calculator
  generate
  /* verilator lint_off WIDTH */
  if (OPTION_DCACHE_WAYS >= 2) begin : gen_u_lru
  /* verilator lint_on WIDTH */
    mor1kx_cache_lru_marocchino
    #(
      .NUMWAYS(OPTION_DCACHE_WAYS) // DCACHE_LRU
    )
    dc_lru
    (
      // Inputs
      .current     (lru_history_curr_s2o), // DCACHE_LRU
      .access      (access_way_for_lru), // DCACHE_LRU
      // Outputs
      .update      (lru_history_next), // DCACHE_LRU
      .lru_post    (lru_way) // DCACHE_LRU
    );
  end
  else begin // single way cache
    assign lru_history_next = 1'b1; // single way cache
    assign lru_way          = 1'b1; // single way cache
  end
  endgenerate


  // Pack TAG-RAM data input
  //  # LRU section
  assign tag_din[TAG_LRU_MSB:TAG_LRU_LSB] = tag_din_lru;
  //  # WAY sections collection
  generate
  for (i = 0; i < OPTION_DCACHE_WAYS; i=i+1) begin : tw_sections
    assign tag_din[(i+1)*TAGMEM_WAY_WIDTH-1:i*TAGMEM_WAY_WIDTH] = tag_din_way[i];
  end
  endgenerate


  // TAG_WR_ADDR
  assign tag_windex = virt_addr_rfl_r[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH]; // re-fill / any-inv / update-LRU

  // TAG_RE_ADDR
  assign tag_rindex = lsu_s1_adv_i ?
                        virt_addr_idx_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH] : // TAG_RE_ADDR if advance stage #1
                        virt_addr_s1o_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH];  // TAG_RE_ADDR if stall   stage #1

  // Read/Write port (*_rwp_*) controls
  wire tag_rwp_we = tag_we & (tag_windex == tag_rindex);
  wire tag_rwp_en = lsu_s1_adv_i | tag_rwp_we;

  // Write-only port (*_wp_*) enable
  wire tag_wp_en = tag_we & (tag_windex != tag_rindex);

  // TAG-RAM instance
  mor1kx_dpram_en_w1st
  #(
    .ADDR_WIDTH     (OPTION_DCACHE_SET_WIDTH), // DCAHCE_TAG_RAM
    .DATA_WIDTH     (TAGMEM_WIDTH), // DCAHCE_TAG_RAM
    .CLEAR_ON_INIT  (OPTION_DCACHE_CLEAR_ON_INIT) // DCAHCE_TAG_RAM
  )
  dc_tag_ram
  (
    // port "a": Read / Write (for RW-conflict case)
    .clk_a          (cpu_clk), // DCAHCE_TAG_RAM
    .en_a           (tag_rwp_en), // DCAHCE_TAG_RAM
    .we_a           (tag_rwp_we), // DCAHCE_TAG_RAM
    .addr_a         (tag_rindex), // DCAHCE_TAG_RAM
    .din_a          (tag_din), // DCAHCE_TAG_RAM
    .dout_a         (tag_dout), // DCAHCE_TAG_RAM
    // port "b": Write if no RW-conflict
    .clk_b          (cpu_clk), // DCAHCE_TAG_RAM
    .en_b           (tag_wp_en), // DCAHCE_TAG_RAM
    .we_b           (1'b1), // DCAHCE_TAG_RAM
    .addr_b         (tag_windex), // DCAHCE_TAG_RAM
    .din_b          (tag_din), // DCAHCE_TAG_RAM
    .dout_b         () // DCAHCE_TAG_RAM
  );



  generate
  /* verilator lint_off WIDTH */
  if (OPTION_DCACHE_SNOOP != "NONE") begin : st_ram
  /* verilator lint_on WIDTH */

    genvar sw1;

    //------------------------------//
    // Stage #1: read SNOOP-TAG-RAM //
    //------------------------------//

    // registering input snoop data
    reg  [OPTION_OPERAND_WIDTH-1:0] s1o_snoop_adr;
    reg                             s1o_snoop_en;
    // ---
    always @(posedge cpu_clk) begin
      s1o_snoop_adr <= snoop_adr_i;
    end
    // ---
    always @(posedge cpu_clk) begin
      if (cpu_rst)
        s1o_snoop_en <= 1'b0;
      else
        s1o_snoop_en <= snoop_en_i;
    end


    //-------------------------------------//
    // Stage #2: latch Snoop-Hit detection //
    //-------------------------------------//

    // Data out of tag memory
    wire       [TAGMEM_WIDTH-1:0] s2t_snoop_dout;
    // Each ways information in the tag memory
    wire   [TAGMEM_WAY_WIDTH-1:0] s2t_snoop_dout_way [OPTION_DCACHE_WAYS-1:0];
    // Whether the way hits
    wire [OPTION_DCACHE_WAYS-1:0] s2t_snoop_hit_way;

    // Shoop-Hit per way
    for (sw1=0; sw1<OPTION_DCACHE_WAYS; sw1=sw1+1) begin : gen_snoop_per_way_hit
      // split by ways
      assign s2t_snoop_dout_way[sw1] = s2t_snoop_dout[(sw1+1)*TAGMEM_WAY_WIDTH-1:sw1*TAGMEM_WAY_WIDTH];
      // check for hit
      assign s2t_snoop_hit_way[sw1] = s1o_snoop_en &
        s2t_snoop_dout_way[sw1][TAGMEM_WAY_VALID] &
        (s2t_snoop_dout_way[sw1][TAG_WIDTH-1:0] ==
         s1o_snoop_adr[OPTION_DCACHE_LIMIT_WIDTH-1:WAY_WIDTH]);
    end

    // Each ways information in the tag memory
    reg      [TAGMEM_WAY_WIDTH-1:0] s2o_snoop_dout_way [OPTION_DCACHE_WAYS-1:0];
    reg      [TAGMEM_WAY_WIDTH-1:0] s3o_snoop_dout_way [OPTION_DCACHE_WAYS-1:0];
    // Whether the way hits
    reg    [OPTION_DCACHE_WAYS-1:0] s2o_snoop_hit_way;
    reg    [OPTION_DCACHE_WAYS-1:0] s3o_snoop_hit_way;
    // Indexing TAG-RAM and SNOOP-TAG-RAM during invalidation
    reg  [OPTION_OPERAND_WIDTH-1:0] s2o_snoop_adr_r;

    // --- propagation ---
    // SNOOP-TAG-RAM data and Snoop-Hit per way
    for (sw1=0; sw1<OPTION_DCACHE_WAYS; sw1=sw1+1) begin : gen_s2o_snoop_latches
      always @(posedge cpu_clk) begin
        s2o_snoop_dout_way[sw1] <= s2t_snoop_dout_way[sw1];
        s2o_snoop_hit_way[sw1]  <= s2t_snoop_hit_way[sw1];
        s3o_snoop_dout_way[sw1] <= s2o_snoop_dout_way[sw1];
        s3o_snoop_hit_way[sw1]  <= s2o_snoop_hit_way[sw1];
      end
    end

    // Indexing TAG-RAM and SNOOP-TAG-RAM during invalidation
    always @(posedge cpu_clk) begin
      s2o_snoop_adr_r <= s1o_snoop_adr;
    end
    // ---
    assign s2o_snoop_adr = s2o_snoop_adr_r;

    // --- applying ---
    // SNOOP-TAG-RAM data and Snoop-Hit per way
    for (sw1=0; sw1<OPTION_DCACHE_WAYS; sw1=sw1+1) begin : gen_inv_snoop_assignement
      assign inv_snoop_dout_way[sw1] = s3o_snoop_dout_way[sw1];
      assign inv_snoop_hit_way[sw1]  = s3o_snoop_hit_way[sw1];
    end

    // Snoop-Hit flag (1-clok length)
    wire   s2t_snoop_hit   = (|s2t_snoop_hit_way);
    reg    s2o_snoop_hit_r;
    assign s2o_snoop_hit   = s2o_snoop_hit_r; // SNOOP-EANBLED
    // ---
    always @(posedge cpu_clk) begin
      if (cpu_rst)
        s2o_snoop_hit_r <= 1'b0;
      else
        s2o_snoop_hit_r <= s2t_snoop_hit;
    end

    // Do Snoop-Invalidation flag (lock LSU)
    reg    s2o_snoop_proc_r;
    assign s2o_snoop_proc_o = s2o_snoop_proc_r; // SNOOP-EANBLED
    // ---
    always @(posedge cpu_clk) begin
      if (cpu_rst)
        s2o_snoop_proc_r <= 1'b0;
      else if (s2t_snoop_hit)
        s2o_snoop_proc_r <= 1'b1;
      else if (dc_inv_by_snoop & (~s2o_snoop_hit))
        s2o_snoop_proc_r <= 1'b0;
    end

    // Drop write-hit if it is snooped
    //  local copy of physical address
    reg [OPTION_OPERAND_WIDTH-1:0] s2o_phys_addr;
    // ---
    always @(posedge cpu_clk) begin
      if (lsu_s2_adv_i)
        s2o_phys_addr <= phys_addr_s2t_i;
    end // @clock
    // ---
    reg    inv_snoop_dc_ack_write_r;
    assign inv_snoop_dc_ack_write = inv_snoop_dc_ack_write_r;
    // --- byte / half-word / word invalidation ----
    always @(posedge cpu_clk) begin
      if (cpu_rst)
        inv_snoop_dc_ack_write_r <= 1'b0;
      else
        inv_snoop_dc_ack_write_r <= s2o_snoop_hit &     // INV-SNOOP-DC-ACK-WRITE
          (s2o_phys_addr[OPTION_OPERAND_WIDTH-1:2] ==   // INV-SNOOP-DC-ACK-WRITE
           s2o_snoop_adr[OPTION_OPERAND_WIDTH-1:2]);    // INV-SNOOP-DC-ACK-WRITE
    end


    //----------------//
    // Snoop TAGs RAM //
    //----------------//

    // Read indexing of SNOOP-TAG-RAM
    wire [OPTION_DCACHE_SET_WIDTH-1:0] snoop_rindex;
    assign snoop_rindex = snoop_adr_i[WAY_WIDTH-1:OPTION_DCACHE_BLOCK_WIDTH];

    // Read / Write port (*_rwp_*) controls
    wire str_rwp_we = tag_we & (tag_windex == snoop_rindex);
    wire str_rwp_en = str_rwp_we | snoop_en_i;

    // Write-only port (*_wp_*) controls
    wire str_wp_en  = tag_we & (tag_windex != snoop_rindex);

    // SNOOP-TAG-RAM instance
    mor1kx_dpram_en_w1st
    #(
      .ADDR_WIDTH     (OPTION_DCACHE_SET_WIDTH), // DCACHE_SNOOP_TAG_RAM
      .DATA_WIDTH     (TAGMEM_WIDTH), // DCACHE_SNOOP_TAG_RAM
      .CLEAR_ON_INIT  (OPTION_DCACHE_CLEAR_ON_INIT) // DCACHE_SNOOP_TAG_RAM
    )
    dc_snoop_tag_ram
    (
      // port "a": Read / Write (for RW-conflict case)
      .clk_a  (cpu_clk), // DCACHE_SNOOP_TAG_RAM
      .en_a   (str_rwp_en), // DCACHE_SNOOP_TAG_RAM
      .we_a   (str_rwp_we), // DCACHE_SNOOP_TAG_RAM
      .addr_a (snoop_rindex), // DCACHE_SNOOP_TAG_RAM
      .din_a  (tag_din), // DCACHE_SNOOP_TAG_RAM
      .dout_a (s2t_snoop_dout), // DCACHE_SNOOP_TAG_RAM
      // port "b": Write if no RW-conflict
      .clk_b  (cpu_clk), // DCACHE_SNOOP_TAG_RAM
      .en_b   (str_wp_en), // DCACHE_SNOOP_TAG_RAM
      .we_b   (1'b1), // DCACHE_SNOOP_TAG_RAM
      .addr_b (tag_windex), // DCACHE_SNOOP_TAG_RAM
      .din_b  (tag_din), // DCACHE_SNOOP_TAG_RAM
      .dout_b () // DCACHE_SNOOP_TAG_RAM
    );

  end
  else begin

    genvar sw2;

    assign s2o_snoop_hit = 1'b0; // SNOOP-DISANBLED
    assign s2o_snoop_proc_o = 1'b0; // SNOOP-DISANBLED

    for (sw2=0; sw2<OPTION_DCACHE_WAYS; sw2=sw2+1) begin : zero_inv_snoop_data
      assign inv_snoop_dout_way[sw2] = {TAGMEM_WAY_WIDTH{1'b0}};  // SNOOP-DISANBLED
      assign inv_snoop_hit_way[sw2]  = 1'b0;                      // SNOOP-DISANBLED
    end

    assign s2o_snoop_adr = {OPTION_OPERAND_WIDTH{1'b0}}; // SNOOP-DISANBLED

    // Drop write-hit if it is snooped
    assign inv_snoop_dc_ack_write = 1'b0; // SNOOP-DISANBLED

  end
  endgenerate

endmodule // mor1kx_dcache_marocchino
