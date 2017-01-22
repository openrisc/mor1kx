////////////////////////////////////////////////////////////////////////
//                                                                    //
//  mor1kx_lsu_marocchino                                             //
//                                                                    //
//  Description: Data bus interface for MAROCCHINO pipeline           //
//               Dbus interface request signal out synchronous        //
//               32-bit specific                                      //
//                                                                    //
//               Derived from mor1kx_lsu_cappuccino                   //
//                                                                    //
////////////////////////////////////////////////////////////////////////
//                                                                    //
//   Copyright (C) 2012 Julius Baxter                                 //
//                      juliusbaxter@gmail.com                        //
//                                                                    //
//   Copyright (C) 2013 Stefan Kristiansson                           //
//                      stefan.kristiansson@saunalahti.fi             //
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

module mor1kx_lsu_marocchino
#(
  parameter OPTION_OPERAND_WIDTH        = 32,
  // data cache
  parameter OPTION_DCACHE_BLOCK_WIDTH   = 5,
  parameter OPTION_DCACHE_SET_WIDTH     = 9,
  parameter OPTION_DCACHE_WAYS          = 2,
  parameter OPTION_DCACHE_LIMIT_WIDTH   = 32,
  parameter OPTION_DCACHE_SNOOP         = "NONE",
  parameter OPTION_DCACHE_CLEAR_ON_INIT = 0,
  // mmu cache
  parameter FEATURE_DMMU_HW_TLB_RELOAD = "NONE",
  parameter OPTION_DMMU_SET_WIDTH      = 6,
  parameter OPTION_DMMU_WAYS           = 1,
  parameter OPTION_DMMU_CLEAR_ON_INIT  = 0,
  // store buffer
  parameter OPTION_STORE_BUFFER_DEPTH_WIDTH   = 4, // 16 taps
  parameter OPTION_STORE_BUFFER_CLEAR_ON_INIT = 0
)
(
  // clocks & resets
  input                                 clk,
  input                                 rst,
  // Pipeline controls
  input                                 pipeline_flush_i,
  input                                 padv_wb_i,
  input                                 grant_wb_to_lsu_i,
  // configuration
  input                                 dc_enable_i,
  input                                 dmmu_enable_i,
  input                                 supervisor_mode_i,
  // Input from DECODE (not latched)
  input      [OPTION_OPERAND_WIDTH-1:0] exec_sbuf_epcr_i,       // for store buffer EPCR computation
  input           [`OR1K_IMM_WIDTH-1:0] exec_lsu_imm16_i, // immediate offset for address computation
  input      [OPTION_OPERAND_WIDTH-1:0] exec_lsu_a1_i,   // operand "A" (part of address)
  input      [OPTION_OPERAND_WIDTH-1:0] exec_lsu_b1_i,   // operand "B" (value to store)
  input                                 exec_op_lsu_load_i,
  input                                 exec_op_lsu_store_i,
  input                                 exec_op_lsu_atomic_i,
  input                           [1:0] exec_lsu_length_i,
  input                                 exec_lsu_zext_i,
  input                                 exec_op_msync_i,
  // SPR interface
  input                          [15:0] spr_bus_addr_i,
  input                                 spr_bus_we_i,
  input                                 spr_bus_stb_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_i,
  output     [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_dc_o,
  output                                spr_bus_ack_dc_o,
  output     [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_dmmu_o,
  output                                spr_bus_ack_dmmu_o,
  // interface to data bus
  output reg [OPTION_OPERAND_WIDTH-1:0] dbus_adr_o,
  output reg                            dbus_req_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] dbus_dat_o,
  output reg                      [3:0] dbus_bsel_o,
  output                                dbus_we_o,
  output                                dbus_burst_o,
  input                                 dbus_err_i,
  input                                 dbus_ack_i,
  input      [OPTION_OPERAND_WIDTH-1:0] dbus_dat_i,
  // Cache sync for multi-core environment
  input                          [31:0] snoop_adr_i,
  input                                 snoop_en_i,
  // Output flags and load result
  output                                lsu_taking_op_o,
  output                                lsu_valid_o, // result ready or exceptions
  output reg [OPTION_OPERAND_WIDTH-1:0] wb_lsu_result_o,
  output reg                            wb_lsu_valid_miss_o,
  output reg                            wb_rfd1_wb_lsu_miss_o,
  output reg                            wb_flag_wb_lsu_miss_o,
  // Exceprions & errors
  //  # Indicator of dbus exception came via the store buffer
  //    and appropriate PC
  output reg [OPTION_OPERAND_WIDTH-1:0] sbuf_eear_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] sbuf_epcr_o,
  output reg                            sbuf_err_o,
  // exception output
  //  # particular LSU exception flags
  output reg                            wb_except_dbus_err_o,
  output reg                            wb_except_dpagefault_o,
  output reg                            wb_except_dtlb_miss_o,
  output reg                            wb_except_dbus_align_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] wb_lsu_except_addr_o,
  //  # combined LSU exceptions flag
  output reg                            wb_an_except_lsu_o,
  // Atomic operation flag set/clear logic
  output reg                            wb_atomic_flag_set_o,
  output reg                            wb_atomic_flag_clear_o
);

  // Input register for DBUS/DCACHE access stage
  //  # load/store
  reg                            cmd_load_r;  // either atomic or not
  reg                            cmd_lwa_r;   // exactly load linked
  reg                            cmd_store_r; // not (!!!) atomic
  reg                            cmd_swa_r;   // atomic only
  reg                      [1:0] cmd_length;
  reg                            cmd_zext;
  reg [OPTION_OPERAND_WIDTH-1:0] cmd_rfb;  // register file B in (store operand)
  //  # registers for store buffer EPCR computation
  reg [OPTION_OPERAND_WIDTH-1:0] cmd_epcr;
  //  # latched virtual address
  reg [OPTION_OPERAND_WIDTH-1:0] virt_addr_cmd;
  //  # l.msync
  reg                            cmd_msync_r;


  // DBUS FSM
  //  # DBUS FSM states
  localparam [4:0] DBUS_IDLE      = 5'b00001, // eq. to DCACHE
                   DMEM_REQ       = 5'b10000,
                   DBUS_READ      = 5'b00010, // eq. to DCACHE
                   DBUS_WRITE     = 5'b00100, // eq. to DCACHE
                   DBUS_DC_REFILL = 5'b01000; // eq. to DCACHE
  //  # DBUS FSM state indicator
  reg        [4:0] dbus_state;
  //  # particular states
  wire             dbus_idle_state  = dbus_state[0];
  wire             dmem_req_state   = dbus_state[4];
  wire             dbus_read_state  = dbus_state[1];
  wire             dbus_write_state = dbus_state[2];
  wire             dc_refill_state  = dbus_state[3];
  //  # DBUS FSM other registers & wires
  reg                               dbus_we;
  reg                               dbus_atomic;
  wire                              dbus_swa_discard; // reservation is lost, execute empty read
  wire                              dbus_swa_success; // l.swa is successfull
  wire                              dbus_swa_ack;     // complete DBUS trunsaction with l.swa
  reg                               sbuf_odata;       // not written data on buffer's output


  // DMMU
  wire                              dmmu_cache_inhibit;
  wire   [OPTION_OPERAND_WIDTH-1:0] phys_addr_cmd;
  /* HW reload TLB related (MAROCCHINO_TODO : not implemented yet)
  wire                              tlb_reload_req;
  wire                              tlb_reload_busy;
  wire [OPTION_OPERAND_WIDTH-1:0]   tlb_reload_addr;
  wire                              tlb_reload_pagefault;
  reg                               tlb_reload_ack;
  reg [OPTION_OPERAND_WIDTH-1:0]    tlb_reload_data;
  wire                              tlb_reload_pagefault_clear;
  reg                               tlb_reload_done; */


  // DCACHE
  wire                              dc_ack;
  wire   [OPTION_OPERAND_WIDTH-1:0] dc_dat;
  wire                              dc_access_read;
  wire                              dc_refill_req;
  reg                               dc_refill_allowed; // combinatorial
  wire   [OPTION_OPERAND_WIDTH-1:0] next_refill_adr;
  wire                              dc_refill_first;
  wire                              dc_refill_last;


  // Store buffer
  wire                              sbuf_write; // without exceptions and pipeline-flush
  wire                              sbuf_we;    // with exceptions and pipeline-flush
  // ---
  wire                              sbuf_rdwr_empty;  // read and write simultaneously if buffer is empty
  wire                              sbuf_re;          // with exceptions and pipeline-flush
  // ---
  wire                              sbuf_full;
  wire                              sbuf_empty;
  wire   [OPTION_OPERAND_WIDTH-1:0] sbuf_epcr;
  wire   [OPTION_OPERAND_WIDTH-1:0] sbuf_virt_addr;
  wire   [OPTION_OPERAND_WIDTH-1:0] sbuf_phys_addr;
  wire   [OPTION_OPERAND_WIDTH-1:0] sbuf_dat;
  wire [OPTION_OPERAND_WIDTH/8-1:0] sbuf_bsel;

  // Atomic operations
  reg    [OPTION_OPERAND_WIDTH-1:0] atomic_addr;
  reg                               atomic_reserve;

  // Snoop (for multicore SoC)
  wire                              snoop_event;
  wire                              snoop_hit;


  // Exceptions detected on DCACHE/DBUS access stage
  // # exceptions related to address computation and conversion
  wire                              except_align;
  wire                              except_dtlb_miss;
  wire                              except_dpagefault;
  // # combination of all previous
  wire                              lsu_excepts_addr;
  // # instant DBUS acceess error
  wire                              dbus_err_instant;
  // # combined of address + DBUS related exceptions
  wire                              lsu_excepts_any; // non-registered

  // Exceptions pending for WB
  reg                               except_dbus_err_p;
  reg                               except_align_p;
  reg                               except_dtlb_miss_p;
  reg                               except_dpagefault_p;
  // # combination of all previous
  reg                               lsu_excepts_any_p; // registered


  // load/store data
  wire   [OPTION_OPERAND_WIDTH-1:0] lsu_ldat; // formated load data
  wire   [OPTION_OPERAND_WIDTH-1:0] lsu_sdat; // formated store data

  // LSU pipe controls
  //  # report on command execution
  wire                              lsu_ack_load;
  reg                               lsu_ack_load_p;  // pending for both atomic and none-atomic
  wire                              lsu_ack_store;
  wire                              lsu_ack_swa;
  reg                               lsu_ack_store_p; // pending both atomic and none-atomic
  //  # LSU's pipe free signals (LSU is able to take next command)
  wire                              lsu_free_load;  // complete load
  wire                              lsu_free_store; // complete store
  wire                              lsu_free_all;   // also includes l.msync, exceptions and flushing
  //  # WB miss processing
  wire                              lsu_miss_load;  // to generate load-miss and all-reasons-miss
  wire                              lsu_miss_store; // to generate all-reasons-miss
  wire                              lsu_miss_on;    // assert overall lsu-valid-miss
  wire                              lsu_miss_off;   // de-assert overall lsu-valid-miss

  // Flushing logic provides continuous clean up output
  // from pipeline-flush till transaction (read/re-fill) completion
  reg                               flush_r;
  wire                              flush_by_ctrl;


  // short names for local use
  localparam LSUOOW = OPTION_OPERAND_WIDTH;


  //-------------------//
  // LSU pipe controls //
  //-------------------//

  // Exceptions detected on DCACHE/DBUS access stage
  //  # exceptions related to address computation and conversion
  assign lsu_excepts_addr  = except_align | except_dtlb_miss | except_dpagefault;
  //  # all exceptions
  assign lsu_excepts_any = lsu_excepts_addr | dbus_err_instant;


  // Signal to take new LSU command (less priority than flushing or exceptions)
  wire lsu_takes_load  = exec_op_lsu_load_i  & lsu_free_all; // for DCACHE mostly
  wire lsu_takes_store = exec_op_lsu_store_i & lsu_free_all; // for DCACHE mostly
  wire lsu_taking_ls   = lsu_takes_load | lsu_takes_store;

  // To advance reservation station
  assign lsu_taking_op_o = lsu_taking_ls | exec_op_msync_i;

  // local variant of grant-wb-to-lsu taking into accaunt speculative miss
  wire grant_wb_to_lsu = (padv_wb_i & grant_wb_to_lsu_i) | wb_lsu_valid_miss_o;

  // l.load completion / waiting / WB-miss
  wire   dbus_ack_load  = (dbus_read_state | dc_refill_first) & dbus_ack_i;
  // ---
  assign lsu_ack_load   = (cmd_load_r & dc_ack) | dbus_ack_load;
  // ---
  assign lsu_free_load  = ((~cmd_load_r) & (~lsu_ack_load_p)) | // LSU free of l.load
                          ((lsu_ack_load | lsu_ack_load_p) & padv_wb_i & grant_wb_to_lsu_i) | // LSU free of l.load (completes, speculative WB hit)
                          (dbus_ack_load & wb_rfd1_wb_lsu_miss_o); // LSU free of l.load (completes, speculative WB miss)
  // --- we check *miss* flags at (padv-wb-i & grant-wb-to-lsu-i) ---
  assign lsu_miss_load  = cmd_load_r & (~dbus_ack_load) & (~dc_ack); // for lsu-rfd1-miss


  // l.store completion / waiting / WB-miss
  assign lsu_ack_store  = sbuf_write; // it already includes cmd_store_r
  // ---
  assign lsu_ack_swa    = cmd_swa_r & dbus_swa_ack; // MAROCCHINO_TODO: just dbus-swa-ack ?
  // ---
  assign lsu_free_store = ((~cmd_store_r) & (~cmd_swa_r) & (~lsu_ack_store_p)) | // LSU free of l.store
                          ((lsu_ack_store | lsu_ack_swa | lsu_ack_store_p) & padv_wb_i & grant_wb_to_lsu_i) | // LSU free of l.store (completes, speculative WB hit)
                          ((lsu_ack_store | lsu_ack_swa) & wb_lsu_valid_miss_o); // LSU free of l.store (completes, speculative WB miss)
  // --- we check *miss* flags at (padv-wb-i & grant-wb-to-lsu-i) ---
  wire   lsu_miss_swa   =  cmd_swa_r   & (~dbus_swa_ack);                // for overall lsu-valid-miss and flag
  assign lsu_miss_store = (cmd_store_r & (~sbuf_write)) | lsu_miss_swa;  // for overall lsu-valid-miss


  // LSU is able to take next command
  assign lsu_free_all = lsu_free_load & lsu_free_store &   // LSU is free
                        (~dc_refill_state)             &   // LSU is free
                        (~cmd_msync_r)                 &   // LSU is free
                        (~snoop_hit)                   &   // LSU is free : MAROCCHINO_TODO: already taken into accaunt by others ?
                        (~lsu_excepts_any_p) & (~flush_r); // LSU is free


  // Assert overall lsu-valid-miss at (padv-wb-i & grant-wb-to-lsu-i)
  assign lsu_miss_on  = lsu_miss_load   | // assert overall lsu-valid-miss
                        lsu_miss_store  | // assert overall lsu-valid-miss
                        snoop_hit;        // assert overall lsu-valid-miss: MAROCCHINO_TODO: already taken into accaunt by others ?

  // De-assert overall lsu-valid-miss
  assign lsu_miss_off = ((dbus_read_state | dc_refill_last) & dbus_ack_i) | // de-assert overall lsu-valid-miss
                        lsu_ack_store  | lsu_ack_swa;                       // de-assert overall lsu-valid-miss
                        /*dbus_ack_load | cmd_store_r | lsu_ack_swa; */


  //----------------------------------------------------//
  // Speculative valid flag to push WB (see OMAN, CTRL) //
  //----------------------------------------------------//

  reg lsu_speculative_valid_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      lsu_speculative_valid_r <= 1'b0;
    else if (lsu_excepts_any | pipeline_flush_i) // drop speculative valid flag
      lsu_speculative_valid_r <= 1'b0;
    else if (lsu_taking_ls)                      // set speculative valid flag
      lsu_speculative_valid_r <= 1'b1;
    else if (padv_wb_i & grant_wb_to_lsu_i)      // drop speculative valid flag
      lsu_speculative_valid_r <= 1'b0;
  end // @clock
  // ---
  assign lsu_valid_o = lsu_speculative_valid_r | lsu_excepts_any_p; // either "ready" or exceptions


  //-------------------------------------------------//
  // flags for speculative LSU completion processing //
  //-------------------------------------------------//

  // Any kind of LSU's ACK miss
  //   - prevents padv-wb in CTRL
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_lsu_valid_miss_o <= 1'b0;
    else if (flush_by_ctrl) // drop any-miss
      wb_lsu_valid_miss_o <= 1'b0;
    else if (padv_wb_i & grant_wb_to_lsu_i) // set any-miss
      wb_lsu_valid_miss_o <= lsu_miss_on;
    else if (wb_lsu_valid_miss_o & lsu_miss_off)
      wb_lsu_valid_miss_o <= 1'b0;
  end // @clock

  // LSU's load ACK miss
  //   - prevents resolving D1 related hazards
  //   - prevents write back to RF
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_rfd1_wb_lsu_miss_o <= 1'b0;
    else if (flush_by_ctrl) // drop load-miss
      wb_rfd1_wb_lsu_miss_o <= 1'b0;
    else if (padv_wb_i & grant_wb_to_lsu_i) // try load-ack at 1st time
      wb_rfd1_wb_lsu_miss_o <= lsu_miss_load;
    else if (wb_rfd1_wb_lsu_miss_o & dbus_ack_load) // padv-wb is blocked, try load-ack continously
      wb_rfd1_wb_lsu_miss_o <= 1'b0;
  end // @clock

  // LSU's l.swa ACK miss
  //   - prevents write back flag nad taking conditional branches
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_flag_wb_lsu_miss_o <= 1'b0;
    else if (flush_by_ctrl) // drop swa-miss
      wb_flag_wb_lsu_miss_o <= 1'b0;
    else if (padv_wb_i & grant_wb_to_lsu_i) // try swa-ack at 1st time
      wb_flag_wb_lsu_miss_o <= lsu_miss_swa;
    else if (wb_flag_wb_lsu_miss_o & dbus_swa_ack) // padv-wb is blocked, try swa-ack continously
      wb_flag_wb_lsu_miss_o <= 1'b0;
  end // @clock


  //-----------------------------------------------------------------//
  // Flushing from pipeline-flush-i till DBUS transaction completion //
  //-----------------------------------------------------------------//

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      flush_r <= 1'b0; // on reset
    else if (flush_r & dbus_idle_state)
      flush_r <= 1'b0; // on de-assert
    else if (~flush_r)
      flush_r <= pipeline_flush_i;
  end // @clock
  // ---
  assign flush_by_ctrl = pipeline_flush_i | flush_r;


  //---------------------------//
  // Address computation stage //
  //---------------------------//

  //   To clean up registers on the stage we use only pipeline-flush, but not flush-r.
  // It makes possible to get next to flush instruction and start execution just after
  // completion DBUS transaction which has been flushed by pipeline flush.

  // compute address
  wire [LSUOOW-1:0] virt_addr = exec_lsu_a1_i + {{(LSUOOW-16){exec_lsu_imm16_i[15]}},exec_lsu_imm16_i};


  //---------------------------//
  // DBUS/DCACHE acceess stage //
  //---------------------------//

  // latches for load (either atomic or not) commands
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      cmd_load_r  <= 1'b0;
      cmd_lwa_r   <= 1'b0;
    end
    else if (lsu_excepts_any | pipeline_flush_i) begin // drop load command (either atomic or not)
      cmd_load_r  <= 1'b0;
      cmd_lwa_r   <= 1'b0;
    end
    else if (lsu_takes_load) begin // latch load command (either atomic or not)
      cmd_load_r  <= 1'b1;
      cmd_lwa_r   <= exec_op_lsu_atomic_i;
    end
    else if (lsu_ack_load) begin
      cmd_load_r  <= 1'b0;
      cmd_lwa_r   <= 1'b0;
    end
  end // @clock

  // latches for none atomic store command
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      cmd_store_r <= 1'b0;
    else if (lsu_excepts_any | pipeline_flush_i) // drop none atomic store command
      cmd_store_r <= 1'b0;
    else if (lsu_takes_store) // latch none atomic store command
      cmd_store_r <= ~exec_op_lsu_atomic_i;
    else if (lsu_ack_store)
      cmd_store_r <= 1'b0;
  end // @clock

  // latches for atomic store command
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      cmd_swa_r <= 1'b0;
    else if (lsu_excepts_any | pipeline_flush_i) // drop atomic store command
      cmd_swa_r <= 1'b0;
    else if (lsu_takes_store) // latch atomic store command
      cmd_swa_r <= exec_op_lsu_atomic_i;
    else if (lsu_ack_swa)
      cmd_swa_r <= 1'b0;
  end // @clock

  // latches for store buffer EPCR
  always @(posedge clk) begin
    if (lsu_takes_store) // store buffer EPCR: doesn't matter atomic or not
      cmd_epcr <= exec_sbuf_epcr_i;
  end // @clock

  // Latch for operand 'B'
  always @(posedge clk) begin
    if (lsu_taking_ls)
      cmd_rfb <= exec_lsu_b1_i;
  end // @clock

  // latch additional parameters of a command
  //       and calculated virtual adderss
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      // additional parameters of a command
      cmd_length    <= 2'd0;
      cmd_zext      <= 1'b0;
      // calculated virtual adderss
      virt_addr_cmd <= {LSUOOW{1'b0}};
    end
    else if (lsu_taking_ls) begin
      // additional parameters of a command
      cmd_length    <= exec_lsu_length_i;
      cmd_zext      <= exec_lsu_zext_i;
      // calculated virtual adderss
      virt_addr_cmd <= virt_addr;
    end
  end // @clock

  // l.msync cause LSU busy
  wire cmd_msync_deassert = cmd_msync_r & (dbus_idle_state & sbuf_empty | dbus_err_instant); // deassert busy by l.msync
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      cmd_msync_r <= 1'b0;
    else if (exec_op_msync_i)
      cmd_msync_r <= 1'b1;
    else if (cmd_msync_deassert)
      cmd_msync_r <= 1'b0;
  end // @clock


  //----------------//
  // LSU exceptions //
  //----------------//

  // --- bus error ---
  assign dbus_err_instant = dbus_req_o & dbus_err_i;

  // --- bus error during bus access from store buffer ---
  //  ## pay attention that l.swa is executed around of
  //     store buffer, so we don't take into accaunt
  //     atomic store here.
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      sbuf_err_o  <= 1'b0;
    else if (flush_by_ctrl) // prevent store buffer DBUS error report
      sbuf_err_o  <= 1'b0;
    else if (dbus_err_instant & dbus_we & ~dbus_atomic)
      sbuf_err_o  <= 1'b1;
  end // @ clock

  // --- addresses for bus error during bus access from store buffer ---
  //  ## pay attention that l.swa is executed around of
  //     store buffer, so we don't take into accaunt
  //     atomic store here.
  always @(posedge clk) begin
    if (dbus_err_instant & dbus_we & ~dbus_atomic) begin
      sbuf_eear_o <= sbuf_virt_addr;
      sbuf_epcr_o <= sbuf_epcr;
    end
  end // @ clock

  // --- align error detection ---
  wire align_err_word  = |virt_addr_cmd[1:0];
  wire align_err_short = virt_addr_cmd[0];

  assign except_align = (cmd_load_r | cmd_store_r | cmd_swa_r) &      // Align Exception: detection enabled
                        (((cmd_length == 2'b10) & align_err_word) |   // Align Exception: wrong word align
                         ((cmd_length == 2'b01) & align_err_short));  // Align Exception: wrong short align

  // --- pending latch for align exception ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      except_align_p <= 1'b0;
    else if (flush_by_ctrl) // drop align exception pending latch
      except_align_p <= 1'b0;
    else if (except_align)
      except_align_p <= 1'b1;
  end // @clock

  // --- pending latch for DBUS error ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      except_dbus_err_p <= 1'b0;
    else if (flush_by_ctrl) // drop DBUS error pending latch
      except_dbus_err_p <= 1'b0;
    else if (dbus_err_instant)
      except_dbus_err_p <= 1'b1;
  end // @clock

  // --- pending latch for DTLB-MISS ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      except_dtlb_miss_p <= 1'b0;
    else if (flush_by_ctrl) // drop DTLB-MISS pending latch
      except_dtlb_miss_p <= 1'b0;
    else if (except_dtlb_miss)
      except_dtlb_miss_p <= 1'b1;
  end // @clock

  // --- pending latch for page fault ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      except_dpagefault_p <= 1'b0;
    else if (flush_by_ctrl)  // drop page fault pending latch
      except_dpagefault_p <= 1'b0;
    else if (except_dpagefault)
      except_dpagefault_p <= 1'b1;
  end // @clock

  // --- pending latch for any LSU exception ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      lsu_excepts_any_p <= 1'b0;
    else if (flush_by_ctrl)  // drop any LSU exception pending latch
      lsu_excepts_any_p <= 1'b0;
    else if (lsu_excepts_any)
      lsu_excepts_any_p <= 1'b1;
  end // @clock


  // WB latches for LSU exceptions
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      //  # particular LSU exception flags
      wb_except_dbus_err_o   <= 1'b0;
      wb_except_dpagefault_o <= 1'b0;
      wb_except_dtlb_miss_o  <= 1'b0;
      wb_except_dbus_align_o <= 1'b0;
      //  # combined LSU exceptions flag
      wb_an_except_lsu_o     <= 1'b0;
    end
    else if (flush_by_ctrl) begin  // drop WB-reported exceptions
      //  # particular LSU exception flags
      wb_except_dbus_err_o   <= 1'b0;
      wb_except_dpagefault_o <= 1'b0;
      wb_except_dtlb_miss_o  <= 1'b0;
      wb_except_dbus_align_o <= 1'b0;
      //  # combined LSU exceptions flag
      wb_an_except_lsu_o     <= 1'b0;
    end
    else if (grant_wb_to_lsu) begin // rise WB-reported exceptions
      //  # particular LSU exception flags
      wb_except_dbus_err_o   <= except_dbus_err_p   | dbus_err_instant;
      wb_except_dpagefault_o <= except_dpagefault_p | except_dpagefault;
      wb_except_dtlb_miss_o  <= except_dtlb_miss_p  | except_dtlb_miss;
      wb_except_dbus_align_o <= except_align_p      | except_align;
      //  # combined LSU exceptions flag
      wb_an_except_lsu_o     <= lsu_excepts_any_p   | lsu_excepts_any;
    end
  end // @clock

  // WB latches RAM address related to an LSU exception
  always @(posedge clk) begin
    if (padv_wb_i & grant_wb_to_lsu_i) // latch WB-reported RAM address related to an LSU exception
      wb_lsu_except_addr_o <= virt_addr_cmd;
  end // @clock



  //-----------------//
  // LSU load output //
  //-----------------//

  assign lsu_ldat = dbus_ack_load ? dbus_dat_i : dc_dat;

  // Select part of bus for load
  reg [LSUOOW-1:0] lsu_ldat_aligned;
  // ---
  always @(virt_addr_cmd[1:0] or lsu_ldat) begin
    // synthesis parallel_case full_case
    case(virt_addr_cmd[1:0])
      2'b00: lsu_ldat_aligned = lsu_ldat;
      2'b01: lsu_ldat_aligned = {lsu_ldat[23:0],8'd0};
      2'b10: lsu_ldat_aligned = {lsu_ldat[15:0],16'd0};
      2'b11: lsu_ldat_aligned = {lsu_ldat[7:0],24'd0};
    endcase
  end

  // Do appropriate extension for load
  reg [LSUOOW-1:0] lsu_ldat_extended;
  // ---
  always @(cmd_zext or cmd_length or lsu_ldat_aligned) begin
    // synthesis parallel_case full_case
    case({cmd_zext, cmd_length})
      3'b100:  lsu_ldat_extended = {24'd0,lsu_ldat_aligned[31:24]}; // lbz
      3'b101:  lsu_ldat_extended = {16'd0,lsu_ldat_aligned[31:16]}; // lhz
      3'b000:  lsu_ldat_extended = {{24{lsu_ldat_aligned[31]}},
                                    lsu_ldat_aligned[31:24]}; // lbs
      3'b001:  lsu_ldat_extended = {{16{lsu_ldat_aligned[31]}},
                                    lsu_ldat_aligned[31:16]}; // lhs
      default: lsu_ldat_extended = lsu_ldat_aligned;
    endcase
  end

  //------------------------------//
  // LSU temporary output storage //
  //------------------------------//

  // pending 'store ready' flag for WB_MUX
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      lsu_ack_store_p <= 1'b0;
    else if (grant_wb_to_lsu | lsu_excepts_any | flush_by_ctrl) // prevent 'store ready' pending
      lsu_ack_store_p <= 1'b0;
    else if (lsu_ack_store | lsu_ack_swa)
      lsu_ack_store_p <= 1'b1;
  end // @clock

  // pending 'load ready' flag for WB_MUX
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      lsu_ack_load_p <= 1'b0;
    else if (grant_wb_to_lsu | lsu_excepts_any | flush_by_ctrl) // prevent 'load ready' pending
      lsu_ack_load_p <= 1'b0;
    else if (lsu_ack_load)
      lsu_ack_load_p <= 1'b1;
  end // @clock

  // pending loaded word
  reg [LSUOOW-1:0] load_result_p;
  // ---
  always @(posedge clk) begin
    if (lsu_ack_load)
      load_result_p <= lsu_ldat_extended;
  end // @clock


  //------------------------------------//
  // LSU load result write-back latches //
  //------------------------------------//

  always @(posedge clk) begin
    if (flush_by_ctrl) begin // clean up LSU result (if missed)
      wb_lsu_result_o <= {LSUOOW{1'b0}};
    end
    else if (padv_wb_i) begin
      if (grant_wb_to_lsu_i)
        wb_lsu_result_o <= lsu_ack_load_p ? load_result_p : lsu_ldat_extended;
      else
        wb_lsu_result_o <= {LSUOOW{1'b0}};
    end
    else if (wb_rfd1_wb_lsu_miss_o & dbus_ack_load) // padv-wb is blocked (see CTRL), latch load-result continously
      wb_lsu_result_o <= lsu_ldat_extended;
  end // @clock


  //----------------------------//
  // LSU formatted store output //
  //----------------------------//

  // Big endian bus mapping
  reg [3:0] dbus_bsel;
  always @(cmd_length or virt_addr_cmd[1:0]) begin
    // synthesis parallel_case full_case
    case (cmd_length)
      2'b00: // byte access
      begin
        // synthesis parallel_case full_case
        case(virt_addr_cmd[1:0])
          2'b00: dbus_bsel = 4'b1000;
          2'b01: dbus_bsel = 4'b0100;
          2'b10: dbus_bsel = 4'b0010;
          2'b11: dbus_bsel = 4'b0001;
        endcase
      end
      2'b01: // halfword access
      begin
        // synthesis parallel_case full_case
        case(virt_addr_cmd[1])
          1'b0: dbus_bsel = 4'b1100;
          1'b1: dbus_bsel = 4'b0011;
        endcase
      end
      2'b10,
      2'b11: dbus_bsel = 4'b1111;
    endcase
  end

  // Data bus mapping for store
  assign lsu_sdat =
    (cmd_length == 2'b00) ? {cmd_rfb[7:0],cmd_rfb[7:0],cmd_rfb[7:0],cmd_rfb[7:0]} : // byte access
    (cmd_length == 2'b01) ? {cmd_rfb[15:0],cmd_rfb[15:0]} : // halfword access
                            cmd_rfb; // word access



  //----------//
  // DBUS FSM //
  //----------//

  assign dbus_burst_o = dc_refill_state & ~dc_refill_last;

  // Slightly subtle, but if there is an atomic store coming out from the
  // store buffer, and the link has been broken while it was waiting there,
  // the bus access is still performed as a (discarded) read.
  assign dbus_we_o = dbus_we & ~dbus_swa_discard;


  // re-filll-allowed corresponds to refill-request position in DBUS FSM
  // !!! exceptions and flushing are already taken into accaunt in DCACHE,
  //     so we don't use them here
  always @(dbus_state or sbuf_odata or cmd_store_r or cmd_swa_r or dc_refill_req) begin
    dc_refill_allowed = 1'b0;
    // synthesis parallel_case full_case
    case (dbus_state)
      DMEM_REQ: begin
        if (sbuf_odata | cmd_store_r | cmd_swa_r) // re-fill not allowed
          dc_refill_allowed = 1'b0;
        else if (dc_refill_req) // it automatically means (l.load & dc-access)
          dc_refill_allowed = 1'b1;
      end
      default: begin
      end
    endcase
  end // always

  // state machine
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      // DBUS controls
      dbus_req_o  <= 1'b0;            // DBUS reset
      dbus_we     <= 1'b0;            // DBUS reset
      dbus_bsel_o <= 4'hf;            // DBUS reset
      dbus_adr_o  <= {LSUOOW{1'b0}};  // DBUS reset
      dbus_dat_o  <= {LSUOOW{1'b0}};  // DBUS reset
      dbus_atomic <= 1'b0;            // DBUS reset
      sbuf_odata  <= 1'b0;            // DBUS reset
      // DBUS FSM state
      dbus_state  <= DBUS_IDLE;       // DBUS reset
    end
    else if (dbus_err_instant) begin // in DBUS FSM: highest priority
      // DBUS controls
      dbus_req_o  <= 1'b0;            // DBUS error
      dbus_we     <= 1'b0;            // DBUS error
      dbus_bsel_o <= 4'hf;            // DBUS error
      dbus_adr_o  <= {LSUOOW{1'b0}};  // DBUS error
      dbus_dat_o  <= {LSUOOW{1'b0}};  // DBUS error
      dbus_atomic <= 1'b0;            // DBUS error
      sbuf_odata  <= 1'b0;            // DBUS error; MAROCCHINO_TODO: force buffer empty by DBUS error ?
      // DBUS FSM state
      dbus_state  <= DBUS_IDLE;       // DBUS error
    end
    else begin
      // process
      // synthesis parallel_case full_case
      case (dbus_state)
        DBUS_IDLE: begin
          if (pipeline_flush_i) // DBUS FSM keep idling
            dbus_state <= DBUS_IDLE;
          else if (lsu_taking_ls) // idle -> dmem req
            dbus_state <= DMEM_REQ;
        end

        DMEM_REQ: begin
          if (sbuf_odata) begin
            // DBUS controls
            //  # buffered data for write == store buffer is not empty
            dbus_req_o  <= 1'b1;            // dmem req -> write : from buffer output
            dbus_we     <= 1'b1;            // dmem req -> write : from buffer output
            dbus_bsel_o <= sbuf_bsel;       // dmem req -> write : from buffer output
            dbus_adr_o  <= sbuf_phys_addr;  // dmem req -> write : from buffer output
            dbus_dat_o  <= sbuf_dat;        // dmem req -> write : from buffer output
            dbus_atomic <= 1'b0;            // dmem req -> write : from buffer output : l.swa goes around buffer
            sbuf_odata  <= 1'b0;            // dmem req -> write : from buffer output
            // DBUS FSM state
            dbus_state  <= DBUS_WRITE;      // dmem req -> write : from buffer output
          end
          else if (lsu_excepts_addr | pipeline_flush_i) begin // dmem req
            dbus_state  <= DBUS_IDLE; // dmem req -> exceptions or pipe flush
          end
          else if (cmd_store_r | cmd_swa_r) begin
            if (~snoop_hit) begin
              // DBUS controls
              //  # no buffered data for write == store buffer is empty
              //    we wrte data in buffer, but it keeps empty in the case
              //    because we also perform implicit instant reading
              dbus_req_o  <= 1'b1;          // dmem req -> write : 1st write in empty buffer
              dbus_we     <= 1'b1;          // dmem req -> write : 1st write in empty buffer
              dbus_bsel_o <= dbus_bsel;     // dmem req -> write : 1st write in empty buffer
              dbus_adr_o  <= phys_addr_cmd; // dmem req -> write : 1st write in empty buffer
              dbus_dat_o  <= lsu_sdat;      // dmem req -> write : 1st write in empty buffer
              dbus_atomic <= cmd_swa_r;     // dmem req -> write : l.swa goes around buffer
              sbuf_odata  <= 1'b0;          // dmem-req -> write : 1st write in empty buffer
              // DBUS FSM state
              dbus_state  <= DBUS_WRITE;
            end
          end
          else if (dc_refill_req) begin // it automatically means (l.load & dc-access)
            dbus_req_o  <= 1'b1;
            dbus_adr_o  <= phys_addr_cmd;
            dbus_state  <= DBUS_DC_REFILL;
          end
          else if (cmd_load_r & ~dc_access_read) begin // not cached or DCACHE is disabled
            dbus_req_o  <= 1'b1;
            dbus_adr_o  <= phys_addr_cmd;
            dbus_bsel_o <= dbus_bsel;
            dbus_state  <= DBUS_READ;
          end
          else if (~lsu_taking_ls) begin // no new memory request
            dbus_state <= DBUS_IDLE;    // no new memory request
          end
        end // idle

        DBUS_DC_REFILL: begin
          if (snoop_hit) begin
            dbus_req_o  <= 1'b0;                                  // DC-REFILL: snoop-hit
            dbus_adr_o  <= {LSUOOW{1'b0}};                        // DC-REFILL: snoop-hit
            dbus_state  <= flush_by_ctrl ? DBUS_IDLE : DMEM_REQ;  // DC-REFILL: snoop-hit
          end
          else if (dbus_ack_i) begin
            dbus_adr_o <= next_refill_adr;    // DC-REFILL: DBUS-ack
            if (dc_refill_last) begin
              dbus_req_o  <= 1'b0;            // DC-REFILL: DBUS-last-ack
              dbus_adr_o  <= {LSUOOW{1'b0}};  // DC-REFILL: DBUS-last-ack
              dbus_state  <= DBUS_IDLE;       // DC-REFILL: DBUS-last-ack
            end
          end
        end // dc-refill

        DBUS_READ: begin
          if (dbus_ack_i) begin
            dbus_req_o  <= 1'b0;                                 // DBUS: read complete
            dbus_bsel_o <= 4'hf;                                 // DBUS: read complete
            dbus_adr_o  <= {LSUOOW{1'b0}};                       // DBUS: read complete
            dbus_state  <= flush_by_ctrl ? DBUS_IDLE : DMEM_REQ; // DBUS: read complete
          end
        end // read

        DBUS_WRITE: begin
          if (dbus_ack_i) begin
            // DBUS controls
            dbus_req_o  <= 1'b0;           // DBUS: write complete
            dbus_we     <= 1'b0;           // DBUS: write complete
            dbus_bsel_o <= 4'hf;           // DBUS: write complete
            dbus_adr_o  <= {LSUOOW{1'b0}}; // DBUS: write complete
            dbus_dat_o  <= {LSUOOW{1'b0}}; // DBUS: write complete
            dbus_atomic <= 1'b0;
            // pending data for write (see also sbuf_re)
            if ((~sbuf_empty) | (sbuf_rdwr_empty & ~(lsu_excepts_addr | pipeline_flush_i))) begin // DBUS: write complete
              sbuf_odata <= 1'b1;     // DBUS: current write complete, process next write
              dbus_state <= DMEM_REQ; // DBUS: current write complete, process next write
            end
            else if (lsu_taking_ls | cmd_load_r | cmd_swa_r)
              dbus_state <= DMEM_REQ;  // DBUS: write complete, no more writes, take new or proc pending command
            else
              dbus_state <= DBUS_IDLE; // DBUS: write complete, no more writes, no new command
          end
        end // write-state

        default: begin
          // DBUS controls
          dbus_req_o  <= 1'b0;            // DBUS deault
          dbus_we     <= 1'b0;            // DBUS deault
          dbus_bsel_o <= 4'hf;            // DBUS deault
          dbus_adr_o  <= {LSUOOW{1'b0}};  // DBUS deault
          dbus_dat_o  <= {LSUOOW{1'b0}};  // DBUS deault
          dbus_atomic <= 1'b0;            // DBUS deault
          sbuf_odata  <= 1'b0;            // DBUS deault
          // DBUS FSM state
          dbus_state  <= DBUS_IDLE;       // DBUS deault
        end
      endcase
    end
  end // @ clock state machine



  //-----------------------//
  // Store buffer instance //
  //-----------------------//

  // store buffer write controls
  assign sbuf_write = cmd_store_r & ~sbuf_full & ~snoop_hit;  // SBUFF write
  // include exceptions and pipe flushing
  assign sbuf_we = sbuf_write & ~(lsu_excepts_any | pipeline_flush_i);


  //
  // store buffer read controls
  //
  // auxiliary: read and write simultaneously if buffer is empty
  assign sbuf_rdwr_empty = cmd_store_r & sbuf_empty & ~snoop_hit;
  //
  //  # in DMEM-REQ state we perform reading only if buffer is empty and no pending data on buffer's output
  //    as a result the buffer keep empty status. At the same time we use data from command latches
  //    (not from buffer's output) for initialize DBUS transaction for the case while store-buffer-write
  //    is used as ACK to report that store is executed
  //  # in WRITE at the end of transactions read next value:
  //     - from empty buffer (keep empty flag, but set sbuf-odata flag, see DBUS state machine)
  //     - from non-empty buffer regardless of exceptions or flushing
  //
  // MAROCCHINO_TODO: force buffer empty by DBUS error ?
  //
  //               in DMEM-REQ state we take into accaunt appropriate exceptions
  assign sbuf_re = (dmem_req_state   & sbuf_rdwr_empty & ~sbuf_odata & ~(lsu_excepts_addr | pipeline_flush_i)) | // SBUFF read, dmem-req
  //               in WRITE state if write request overlaps DBUS ACK and empty buffer state
                   (dbus_write_state & dbus_ack_i & sbuf_rdwr_empty & ~(lsu_excepts_addr | pipeline_flush_i))  | // SBUFF read, dbus-write
  //               in WRITE state we read non-empty buffer to prepare next write
                   (dbus_write_state & dbus_ack_i & ~sbuf_empty); // SBUFF read, dbus-write


  // store buffer module
  mor1kx_store_buffer_marocchino
  #(
    .DEPTH_WIDTH          (OPTION_STORE_BUFFER_DEPTH_WIDTH), // STORE_BUFFER
    .OPTION_OPERAND_WIDTH (OPTION_OPERAND_WIDTH), // STORE_BUFFER
    .CLEAR_ON_INIT        (OPTION_STORE_BUFFER_CLEAR_ON_INIT) // STORE_BUFFER
  )
  u_store_buffer
  (
    .clk          (clk), // STORE_BUFFER
    .rst          (rst), // STORE_BUFFER
    // entry port
    .sbuf_epcr_i  (cmd_epcr), // STORE_BUFFER
    .virt_addr_i  (virt_addr_cmd), // STORE_BUFFER
    .phys_addr_i  (phys_addr_cmd), // STORE_BUFFER
    .dat_i        (lsu_sdat), // STORE_BUFFER
    .bsel_i       (dbus_bsel), // STORE_BUFFER
    .write_i      (sbuf_we), // STORE_BUFFER
    // output port
    .sbuf_epcr_o  (sbuf_epcr), // STORE_BUFFER
    .virt_addr_o  (sbuf_virt_addr), // STORE_BUFFER
    .phys_addr_o  (sbuf_phys_addr), // STORE_BUFFER
    .dat_o        (sbuf_dat), // STORE_BUFFER
    .bsel_o       (sbuf_bsel), // STORE_BUFFER
    .read_i       (sbuf_re), // STORE_BUFFER
    // status flags
    .full_o       (sbuf_full), // STORE_BUFFER
    .empty_o      (sbuf_empty) // STORE_BUFFER
  );


  // We have to mask out our own snooped bus access
  assign snoop_event = (snoop_en_i & ~((snoop_adr_i == dbus_adr_o) & dbus_ack_i)) &
                       (OPTION_DCACHE_SNOOP != "NONE");


  //-------------------------//
  // Atomic operations logic //
  //-------------------------//
  assign dbus_swa_discard = dbus_atomic & ~atomic_reserve;
  // ---
  assign dbus_swa_ack     = dbus_atomic & dbus_ack_i;
  // ---
  assign dbus_swa_success = dbus_swa_ack &  atomic_reserve; // for WB & DCACHE
  wire   dbus_swa_fail    = dbus_swa_ack & ~atomic_reserve; // for WB
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      atomic_reserve <= 1'b0;
      atomic_addr    <= {LSUOOW{1'b0}};
    end
    else if (lsu_excepts_any | pipeline_flush_i |                 // drop atomic reserve
             dbus_swa_ack |                                       // drop atomic reserve
             (cmd_store_r & (phys_addr_cmd == atomic_addr)) |     // drop atomic reserve
             (snoop_event & (snoop_adr_i == atomic_addr))) begin  // drop atomic reserve
      atomic_reserve <= 1'b0;
      atomic_addr    <= {LSUOOW{1'b0}};
    end
    else if (cmd_lwa_r) begin
      if (snoop_event & (snoop_adr_i == phys_addr_cmd)) begin
        atomic_reserve <= 1'b0;
        atomic_addr    <= {LSUOOW{1'b0}};
      end
      else if (lsu_ack_load) begin
        atomic_reserve <= 1'b1;
        atomic_addr    <= phys_addr_cmd;
      end
    end
  end // @clock

  // pending atomic flag/set clear responce
  reg atomic_flag_set_p;
  reg atomic_flag_clear_p;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      atomic_flag_set_p   <= 1'b0;
      atomic_flag_clear_p <= 1'b0;
    end
    else if (grant_wb_to_lsu | lsu_excepts_any | flush_by_ctrl) begin // prevent set/clear atomic flag pending
      atomic_flag_set_p   <= 1'b0;
      atomic_flag_clear_p <= 1'b0;
    end
    else if (dbus_swa_ack) begin
      atomic_flag_set_p   <=  atomic_reserve;
      atomic_flag_clear_p <= ~atomic_reserve;
    end
  end // @clock

  // atomic flags for WB_MUX
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      wb_atomic_flag_set_o   <= 1'b0;
      wb_atomic_flag_clear_o <= 1'b0;
    end
    else if (lsu_excepts_any | flush_by_ctrl) begin // drop WB atomic flags
      wb_atomic_flag_set_o   <= 1'b0;
      wb_atomic_flag_clear_o <= 1'b0;
    end
    else if (padv_wb_i) begin
      if (grant_wb_to_lsu_i) begin // conditions for WB atomic flags
        wb_atomic_flag_set_o   <= dbus_swa_success | atomic_flag_set_p;
        wb_atomic_flag_clear_o <= dbus_swa_fail    | atomic_flag_clear_p;
      end
      else begin
        wb_atomic_flag_set_o   <= 1'b0;
        wb_atomic_flag_clear_o <= 1'b0;
      end
    end
    else if (wb_flag_wb_lsu_miss_o) begin
      wb_atomic_flag_set_o   <= dbus_swa_success;
      wb_atomic_flag_clear_o <= dbus_swa_fail;
    end
  end // @clock


  //--------------------//
  // SPR access support //
  //--------------------//
  //   For MAROCCHINO SPR access means that pipeline is stalled till ACK.
  // So, no padv-*. We only delay SPR access command till DBUS transaction
  // completion.
  wire spr_bus_stb_lsu = spr_bus_stb_i & dbus_idle_state; // SPR access


  //-------------------//
  // Instance of cache //
  //-------------------//

  wire dc_store_allowed = lsu_ack_store | dbus_swa_success;

  mor1kx_dcache_marocchino
  #(
    .OPTION_OPERAND_WIDTH         (OPTION_OPERAND_WIDTH), // DCACHE
    .OPTION_DCACHE_BLOCK_WIDTH    (OPTION_DCACHE_BLOCK_WIDTH), // DCACHE
    .OPTION_DCACHE_SET_WIDTH      (OPTION_DCACHE_SET_WIDTH), // DCACHE
    .OPTION_DCACHE_WAYS           (OPTION_DCACHE_WAYS), // DCACHE
    .OPTION_DCACHE_LIMIT_WIDTH    (OPTION_DCACHE_LIMIT_WIDTH), // DCACHE
    .OPTION_DCACHE_SNOOP          (OPTION_DCACHE_SNOOP), // DCACHE
    .OPTION_DCACHE_CLEAR_ON_INIT  (OPTION_DCACHE_CLEAR_ON_INIT) // DCACHE
  )
  u_dcache
  (
    // clock & reset
    .clk                        (clk), // DCACHE
    .rst                        (rst), // DCACHE
    // pipe controls
    .lsu_takes_load_i           (lsu_takes_load), // DCACHE
    .lsu_takes_store_i          (lsu_takes_store), // DCACHE
    .pipeline_flush_i           (pipeline_flush_i), // DCACHE
    // configuration
    .enable_i                   (dc_enable_i), // DCACHE
    // exceptions
    .lsu_excepts_addr_i         (lsu_excepts_addr), // DCACHE
    .dbus_err_i                 (dbus_err_i), // DCACHE
    // Regular operation
    //  # addresses and "DCHACHE inhibit" flag
    .virt_addr_i                (virt_addr), // DCACHE
    .virt_addr_cmd_i            (virt_addr_cmd), // DCACHE
    .phys_addr_cmd_i            (phys_addr_cmd), // DCACHE
    .dmmu_cache_inhibit_i       (dmmu_cache_inhibit), // DCACHE
    //  # DCACHE regular answer
    .dc_access_read_o           (dc_access_read), // DCACHE
    .dc_ack_o                   (dc_ack), // DCACHE
    .dc_dat_o                   (dc_dat), // DCACHE
    //  # STORE format / store data / do|cancel storing
    .dbus_bsel_i                (dbus_bsel), // DCACHE
    .dbus_sdat_i                (lsu_sdat), // DCACHE
    .dc_store_allowed_i         (dc_store_allowed), // DCACHE
    .dbus_swa_discard_i         (dbus_swa_discard), // DCACHE
    // re-fill
    .dc_refill_req_o            (dc_refill_req), // DCACHE
    .dc_refill_allowed_i        (dc_refill_allowed), // DCACHE
    .next_refill_adr_o          (next_refill_adr), // DCACHE
    .refill_first_o             (dc_refill_first), // DCACHE
    .refill_last_o              (dc_refill_last), // DCACHE
    .dbus_dat_i                 (dbus_dat_i), // DCACHE
    .dbus_ack_i                 (dbus_ack_i), // DCACHE
    // SNOOP
    .snoop_adr_i                (snoop_adr_i[31:0]), // DCACHE
    .snoop_event_i              (snoop_event), // DCACHE
    .snoop_hit_o                (snoop_hit), // DCACHE
    // SPR interface
    .spr_bus_addr_i             (spr_bus_addr_i[15:0]), // DCACHE
    .spr_bus_we_i               (spr_bus_we_i), // DCACHE
    .spr_bus_stb_i              (spr_bus_stb_lsu), // DCACHE
    .spr_bus_dat_i              (spr_bus_dat_i), // DCACHE
    .spr_bus_dat_o              (spr_bus_dat_dc_o), // DCACHE
    .spr_bus_ack_o              (spr_bus_ack_dc_o) // DCACHE
  );



  //------------------//
  // Instance of DMMU //
  //------------------//

  mor1kx_dmmu_marocchino
  #(
    .FEATURE_DMMU_HW_TLB_RELOAD (FEATURE_DMMU_HW_TLB_RELOAD), // DMMU
    .OPTION_OPERAND_WIDTH       (OPTION_OPERAND_WIDTH), // DMMU
    .OPTION_DMMU_SET_WIDTH      (OPTION_DMMU_SET_WIDTH), // DMMU
    .OPTION_DMMU_WAYS           (OPTION_DMMU_WAYS), // DMMU
    .OPTION_DMMU_CLEAR_ON_INIT  (OPTION_DMMU_CLEAR_ON_INIT) // DMMU
  )
  u_dmmu
  (
    // clocks and resets
    .clk                              (clk), // DMMU
    .rst                              (rst), // DMMU
    // pipe controls
    .lsu_takes_ls_i                   (lsu_taking_ls), // DMMU
    .pipeline_flush_i                 (pipeline_flush_i), // DMMU
    // exceptions
    .lsu_excepts_any_i                (lsu_excepts_any), // DMMU
    // configuration and commands
    .enable_i                         (dmmu_enable_i), // DMMU
    .supervisor_mode_i                (supervisor_mode_i), // DMMU
    .lsu_store_i                      (exec_op_lsu_store_i), // DMMU
    .lsu_load_i                       (exec_op_lsu_load_i), // DMMU
    // address translation
    .virt_addr_i                      (virt_addr), // DMMU
    .virt_addr_cmd_i                  (virt_addr_cmd), // DMMU
    .phys_addr_cmd_o                  (phys_addr_cmd), // DMMU
    // translation flags
    .cache_inhibit_o                  (dmmu_cache_inhibit), // DMMU
    .tlb_miss_o                       (except_dtlb_miss), // DMMU
    .pagefault_o                      (except_dpagefault), // DMMU
    // HW TLB reload face.  MAROCCHINO_TODO: not implemented
    .tlb_reload_ack_i                 (1'b0), // DMMU
    .tlb_reload_data_i                ({LSUOOW{1'b0}}), // DMMU
    .tlb_reload_pagefault_clear_i     (1'b0), // DMMU
    .tlb_reload_req_o                 (), // DMMU
    .tlb_reload_busy_o                (), // DMMU
    .tlb_reload_addr_o                (), // DMMU
    .tlb_reload_pagefault_o           (), // DMMU
    // SPR bus
    .spr_bus_addr_i                   (spr_bus_addr_i[15:0]), // DMMU
    .spr_bus_we_i                     (spr_bus_we_i), // DMMU
    .spr_bus_stb_i                    (spr_bus_stb_lsu), // DMMU
    .spr_bus_dat_i                    (spr_bus_dat_i), // DMMU
    .spr_bus_dat_o                    (spr_bus_dat_dmmu_o), // DMMU
    .spr_bus_ack_o                    (spr_bus_ack_dmmu_o) // DMMU
  );

endmodule // mor1kx_lsu_marocchino
