/* ****************************************************************************
  This Source Code Form is subject to the terms of the
  Open Hardware Description License, v. 1.0. If a copy
  of the OHDL was not distributed with this file, You
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: Data bus interface for MAROCCHINO pipeline

  Dbus interface request signal out synchronous
  32-bit specific
  Derived from mor1kx_lsu_cappuccino

  Copyright (C) 2012 Julius Baxter <juliusbaxter@gmail.com>
  Copyright (C) 2013 Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>
  Copyright (C) 2015 Andrey Bacherov <avbacherov@opencores.org>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_lsu_marocchino
#(
  // data cache
  parameter OPTION_OPERAND_WIDTH      = 32,
  parameter OPTION_DCACHE_BLOCK_WIDTH = 5,
  parameter OPTION_DCACHE_SET_WIDTH   = 9,
  parameter OPTION_DCACHE_WAYS        = 2,
  parameter OPTION_DCACHE_LIMIT_WIDTH = 32,
  parameter OPTION_DCACHE_SNOOP       = "NONE",
  // mmu cache
  parameter FEATURE_DMMU_HW_TLB_RELOAD = "NONE",
  parameter OPTION_DMMU_SET_WIDTH      = 6,
  parameter OPTION_DMMU_WAYS           = 1,
  // store buffer
  parameter FEATURE_STORE_BUFFER            = "ENABLED",
  parameter OPTION_STORE_BUFFER_DEPTH_WIDTH = 8
)
(
  // clocks & resets
  input                                 clk,
  input                                 rst,
  // Pipeline controls
  input                                 pipeline_flush_i,
  input                                 padv_decode_i,
  input                                 padv_wb_i,
  input                                 do_rf_wb_i,
  input                                 grant_wb_to_lsu_i,
  // configuration
  input                                 dc_enable_i,
  input                                 dmmu_enable_i,
  input                                 supervisor_mode_i,
  // Input from DECODE (not latched)
  input           [`OR1K_IMM_WIDTH-1:0] dcod_imm16_i, // immediate offset for address computation
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_rfa_i,   // operand "A" (part of address)
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_rfb_i,   // operand "B" (value to store)
  input                                 dcod_op_lsu_load_i,
  input                                 dcod_op_lsu_store_i,
  input                                 dcod_op_lsu_atomic_i,
  input                           [1:0] dcod_lsu_length_i,
  input                                 dcod_lsu_zext_i,
  input                                 dcod_op_msync_i,
  //   forwarding from WB
  input                                 exe2dec_hazard_a_i,
  input                                 exe2dec_hazard_b_i,
  input      [OPTION_OPERAND_WIDTH-1:0] wb_result_i,
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
  output     [OPTION_OPERAND_WIDTH-1:0] dbus_adr_o,
  output reg                            dbus_req_o,
  output     [OPTION_OPERAND_WIDTH-1:0] dbus_dat_o,
  output reg                      [3:0] dbus_bsel_o,
  output                                dbus_we_o,
  output                                dbus_burst_o,
  input                                 dbus_err_i,
  input                                 dbus_ack_i,
  input      [OPTION_OPERAND_WIDTH-1:0] dbus_dat_i,
  // Cache sync for multi-core environment
  input                          [31:0] snoop_adr_i,
  input                                 snoop_en_i,
  // Exceprions & errors
  //  # Indicator of dbus exception came via the store buffer
  //    and appropriate PC
  output     [OPTION_OPERAND_WIDTH-1:0] store_buffer_epcr_o,
  output reg                            store_buffer_err_o,
  //  # From control stage, exception PC for the store buffer input
  input      [OPTION_OPERAND_WIDTH-1:0] ctrl_epcr_i,
  output                                lsu_excepts_o,
  // output flags and load result
  output                                lsu_busy_o,
  output                                lsu_valid_o,
  output     [OPTION_OPERAND_WIDTH-1:0] lsu_adr_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] wb_lsu_result_o,
  output reg                            wb_lsu_rdy_o,
  // exception output
  output reg                            wb_except_dbus_o,
  output reg                            wb_except_dpagefault_o,
  output reg                            wb_except_dtlb_miss_o,
  output reg                            wb_except_align_o,
  // Atomic operation flag set/clear logic
  output reg                            wb_atomic_flag_set_o,
  output reg                            wb_atomic_flag_clear_o
);

  reg                               dbus_ack;
  reg                               dbus_err;
  reg [OPTION_OPERAND_WIDTH-1:0]    dbus_dat;
  reg [OPTION_OPERAND_WIDTH-1:0]    dbus_adr;
  wire [OPTION_OPERAND_WIDTH-1:0]   next_dbus_adr;
  reg                               dbus_we;
  wire                              dbus_access;
  wire                              dbus_stall;

  wire [OPTION_OPERAND_WIDTH-1:0]   lsu_ldat;
  wire [OPTION_OPERAND_WIDTH-1:0]   lsu_sdat;
  wire                              lsu_ack;

  wire                              dc_err;
  wire                              dc_ack;
  wire [31:0]                       dc_ldat;
  wire [31:0]                       dc_sdat;
  wire [31:0]                       dc_adr;
  wire [31:0]                       dc_adr_match;
  wire                              dc_req;
  wire                              dc_we;
  wire [3:0]                        dc_bsel;

  wire                              dc_access;
  wire                              dc_refill_allowed;
  wire                              dc_refill;
  wire                              dc_refill_req;
  wire                              dc_refill_done;

  reg                               dc_enable_r;
  wire                              dc_enabled;

  // DMMU
  wire                              tlb_miss;
  wire                              dmmu_pagefault;
  wire [OPTION_OPERAND_WIDTH-1:0]   dmmu_phys_addr;
  wire                              dmmu_cache_inhibit;

  wire                              tlb_reload_req;
  wire                              tlb_reload_busy;
  wire [OPTION_OPERAND_WIDTH-1:0]   tlb_reload_addr;
  wire                              tlb_reload_pagefault;
  reg                               tlb_reload_ack;
  reg [OPTION_OPERAND_WIDTH-1:0]    tlb_reload_data;
  wire                              tlb_reload_pagefault_clear;
  reg                               tlb_reload_done;

  // Store buffer
  wire                              store_buffer_write;
  wire                              store_buffer_read;
  wire                              store_buffer_full;
  wire                              store_buffer_empty;
  wire [OPTION_OPERAND_WIDTH-1:0]   store_buffer_radr;
  wire [OPTION_OPERAND_WIDTH-1:0]   store_buffer_wadr;
  wire [OPTION_OPERAND_WIDTH-1:0]   store_buffer_dat;
  wire [OPTION_OPERAND_WIDTH/8-1:0] store_buffer_bsel;
  wire                              store_buffer_atomic;
  reg                               store_buffer_write_pending;

  reg                               dbus_atomic;

  reg                               last_write;
  reg                               write_done;

  // Atomic operations
  reg [OPTION_OPERAND_WIDTH-1:0]    atomic_addr;
  reg                               atomic_reserve;

  wire                              snoop_valid;
  wire                              dc_snoop_hit;

  wire                              except_align;
  wire                              except_dbus_err;
  wire                              except_dtlb_miss;
  wire                              except_dpagefault;

  wire                              msync_busy; // busy due to memory sync. proceedings
  wire                              msync_done;


  // registers for command from DECODE
  reg                            lsu_load_r;
  reg                            lsu_store_r;
  reg                            lsu_atomic_r;
  reg                      [1:0] lsu_length_r;
  reg                            lsu_zext_r;

  // registers for operands from DECODE
  reg      [`OR1K_IMM_WIDTH-1:0] lsu_imm16_r; // immediate offset for address computation
  reg [OPTION_OPERAND_WIDTH-1:0] lsu_a_r;     // operand "A" (part of address)
  reg [OPTION_OPERAND_WIDTH-1:0] lsu_b_r;     // operand "B" (value to store)

  // operands after frorwarding from WB
  wire [OPTION_OPERAND_WIDTH-1:0] lsu_a;
  wire [OPTION_OPERAND_WIDTH-1:0] lsu_b;

  // registers for support forwarding forwarding
  reg                            lsu_fwd_wb_a_r; // use WB result
  reg                            lsu_fwd_wb_b_r; // use WB result

  // load/store
  wire dcod_op_ls = dcod_op_lsu_load_i | dcod_op_lsu_store_i; // input is load/store
  wire op_ls      = lsu_load_r | lsu_store_r; // latched load/store

  // signal to take new LSU command (less priority than flushing)
  wire take_op_ls = op_ls & (~pipeline_flush_i) & (~except_align);
  

  // --- latch load/store commands ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      lsu_load_r   <= 1'b0;
      lsu_store_r  <= 1'b0;
      lsu_atomic_r <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      lsu_load_r   <= 1'b0;
      lsu_store_r  <= 1'b0;
      lsu_atomic_r <= 1'b0;
    end
    else if (padv_decode_i & dcod_op_ls) begin
      lsu_load_r   <= dcod_op_lsu_load_i;
      lsu_store_r  <= dcod_op_lsu_store_i;
      lsu_atomic_r <= dcod_op_lsu_atomic_i;
    end
    else if (take_op_ls) begin
      lsu_load_r   <= 1'b0;
      lsu_store_r  <= 1'b0;
      lsu_atomic_r <= 1'b0;
    end
  end // @clock

  // --- latch various load/store attributes and address offset ---
  always @(posedge clk) begin
    if (padv_decode_i & dcod_op_ls) begin
      lsu_imm16_r  <= dcod_imm16_i;
      lsu_length_r <= dcod_lsu_length_i;
      lsu_zext_r   <= dcod_lsu_zext_i;
    end
  end // @clock

  // --- latch forwarding flags ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      lsu_fwd_wb_a_r <= 1'b0;
      lsu_fwd_wb_b_r <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      lsu_fwd_wb_a_r <= 1'b0;
      lsu_fwd_wb_b_r <= 1'b0;
    end
    else if (padv_decode_i & dcod_op_ls) begin
      lsu_fwd_wb_a_r <= exe2dec_hazard_a_i;
      lsu_fwd_wb_b_r <= exe2dec_hazard_b_i; 
    end
    else if (take_op_ls) begin
      lsu_fwd_wb_a_r <= 1'b0;
      lsu_fwd_wb_b_r <= 1'b0;
    end
  end // @clock

  // --- opernands ---
  always @(posedge clk) begin
    if (padv_decode_i & dcod_op_ls) begin
      lsu_a_r <= dcod_rfa_i;
      lsu_b_r <= dcod_rfb_i;
    end
    else if (take_op_ls) begin
      lsu_a_r <= lsu_a;
      lsu_b_r <= lsu_b;
    end
  end // @clock

  // operands with forwarding from WB
  assign lsu_a = lsu_fwd_wb_a_r ? wb_result_i : lsu_a_r;
  assign lsu_b = lsu_fwd_wb_b_r ? wb_result_i : lsu_b_r;

  // compute address
  wire [OPTION_OPERAND_WIDTH-1:0] lsu_addr =
    lsu_a + {{(OPTION_OPERAND_WIDTH-16){lsu_imm16_r[15]}},lsu_imm16_r};



  // one more latches
  reg                            cmd_load;
  reg                            cmd_store;
  reg                            cmd_atomic;
  reg                            cmd_ls;
  reg                            cmd_lwa, cmd_swa; // load/store atomic
  reg                      [1:0] cmd_length;
  reg                            cmd_zext;
  reg [OPTION_OPERAND_WIDTH-1:0] cmd_addr; // calculated address from ALU
  reg [OPTION_OPERAND_WIDTH-1:0] cmd_rfb;  // register file B in (store operand)
  // lsu local latched commands
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      cmd_load   <= 1'b0;
      cmd_store  <= 1'b0;
      cmd_atomic <= 1'b0;
      cmd_ls     <= 1'b0;
      cmd_lwa    <= 1'b0;
      cmd_swa    <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      cmd_load   <= 1'b0;
      cmd_store  <= 1'b0;
      cmd_atomic <= 1'b0;
      cmd_ls     <= 1'b0;
      cmd_lwa    <= 1'b0;
      cmd_swa    <= 1'b0;
    end
    else if (take_op_ls) begin
      cmd_load   <= lsu_load_r;
      cmd_store  <= lsu_store_r;
      cmd_atomic <= lsu_atomic_r;
      cmd_ls     <= op_ls;
      cmd_lwa    <= lsu_load_r  & lsu_atomic_r;
      cmd_swa    <= lsu_store_r & lsu_atomic_r;
    end
    else if (lsu_ack) begin
      cmd_load   <= 1'b0;
      cmd_store  <= 1'b0;
      cmd_atomic <= 1'b0;
      cmd_ls     <= 1'b0;
      cmd_lwa    <= 1'b0;
      cmd_swa    <= 1'b0;
    end
  end // @clock

  // lsu local latched additional parameters
  always @(posedge clk) begin
    if (take_op_ls) begin
      cmd_length <= lsu_length_r;
      cmd_zext   <= lsu_zext_r;
      cmd_addr   <= lsu_addr;
      cmd_rfb    <= lsu_b;
    end
  end // @clock

  // output latched address for exceptions processing
  assign lsu_adr_o = cmd_addr;

  // lsu new command 1-clock mask
  reg cmd_new;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      cmd_new <= 1'b0;
    else
      cmd_new <= take_op_ls;
  end // @clock

  // l.msync to generate msync-stall
  reg  lsu_msync_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      lsu_msync_r <= 1'b0;
    else if (pipeline_flush_i)
      lsu_msync_r <= 1'b0;
    else if (dcod_op_msync_i)
      lsu_msync_r <= 1'b1;
    else
      lsu_msync_r <= 1'b0;
  end // @clock
  // ---
  reg  cmd_op_msync;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      cmd_op_msync <= 1'b0;
    else if (pipeline_flush_i)
      cmd_op_msync <= 1'b0;
    else if (lsu_msync_r)
      cmd_op_msync <= 1'b1;
    else if (msync_done)
      cmd_op_msync <= 1'b0;
  end // @clock

  // registers for temporary exception storing
  reg lsu_except_dbus_r;
  reg lsu_except_align_r;
  reg lsu_except_dtlb_miss_r;
  reg lsu_except_dpagefault_r;
  // latching
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      lsu_except_dbus_r       <= 1'b0;
      lsu_except_align_r      <= 1'b0;
      lsu_except_dtlb_miss_r  <= 1'b0;
      lsu_except_dpagefault_r <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      lsu_except_dbus_r       <= 1'b0;
      lsu_except_align_r      <= 1'b0;
      lsu_except_dtlb_miss_r  <= 1'b0;
      lsu_except_dpagefault_r <= 1'b0;
    end
    else begin
      if (except_dbus_err)
        lsu_except_dbus_r       <= 1'b1;
      if (except_align)
        lsu_except_align_r      <= 1'b1;
      if (except_dtlb_miss)
        lsu_except_dtlb_miss_r  <= 1'b1;
      if (except_dpagefault)
        lsu_except_dpagefault_r <= 1'b1;
    end
  end // @clock
  // output assignement
  assign lsu_excepts_o = lsu_except_dbus_r      | lsu_except_align_r |
                         lsu_except_dtlb_miss_r | lsu_except_dpagefault_r;

  // WB latches for LSU EXCEPTIONS
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      wb_except_dbus_o       <= 1'b0;
      wb_except_dpagefault_o <= 1'b0;
      wb_except_dtlb_miss_o  <= 1'b0;
      wb_except_align_o      <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      wb_except_dbus_o       <= 1'b0;
      wb_except_dpagefault_o <= 1'b0;
      wb_except_dtlb_miss_o  <= 1'b0;
      wb_except_align_o      <= 1'b0;
    end
    else if (padv_wb_i & grant_wb_to_lsu_i) begin
      wb_except_dbus_o       <= lsu_except_dbus_r;
      wb_except_dpagefault_o <= lsu_except_dpagefault_r;
      wb_except_dtlb_miss_o  <= lsu_except_dtlb_miss_r;
      wb_except_align_o      <= lsu_except_align_r;
    end
  end // @clock

  //----------------------//
  // Exceptions detection //
  //----------------------//

  // --- align ---
  wire align_err_word  = |lsu_addr[1:0];
  wire align_err_short = lsu_addr[0];

  assign except_align = op_ls &
                        (((lsu_length_r == 2'b10) & align_err_word) |
                         ((lsu_length_r == 2'b01) & align_err_short));


  // --- any bus error ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      dbus_err <= 1'b0;
    else if (pipeline_flush_i)
      dbus_err <= 1'b0;
    else if (dbus_err_i)
      dbus_err <= 1'b1;
  end // @ clock
  // --- write bus error ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      store_buffer_err_o <= 1'b0;
    else if (pipeline_flush_i)
      store_buffer_err_o <= 1'b0;
    else if (dbus_err_i & dbus_we_o)
      store_buffer_err_o <= 1'b1;
  end // @ clock
  // --- combined bus errors ---
  assign except_dbus_err = dbus_err | store_buffer_err_o;

  // --- D-TLB miss ---
  assign except_dtlb_miss =
    cmd_ls & dmmu_enable_i & tlb_miss & (~tlb_reload_busy);

  // --- Page fault ---
  assign except_dpagefault =
    tlb_reload_pagefault |
    (cmd_ls & dmmu_enable_i & dmmu_pagefault & (~tlb_reload_busy));

  // --- combined exception flag (local use) ---
  wire lsu_excepts = except_dbus_err  | except_align |
                     except_dtlb_miss | except_dpagefault;


  //------------//
  // LSU output //
  //------------//

  // Big endian bus mapping
  reg [3:0] dbus_bsel;
  always @(*)
    case (cmd_length)
      2'b00: // byte access
        case(cmd_addr[1:0])
          2'b00: dbus_bsel = 4'b1000;
          2'b01: dbus_bsel = 4'b0100;
          2'b10: dbus_bsel = 4'b0010;
          2'b11: dbus_bsel = 4'b0001;
        endcase
      2'b01: // halfword access
        case(cmd_addr[1])
          1'b0: dbus_bsel = 4'b1100;
          1'b1: dbus_bsel = 4'b0011;
        endcase
      2'b10,
      2'b11: dbus_bsel = 4'b1111;
    endcase

  // Select part of bus for load
  reg [OPTION_OPERAND_WIDTH-1:0] dbus_dat_aligned;
  always @(*)
    case(cmd_addr[1:0])
      2'b00: dbus_dat_aligned = lsu_ldat;
      2'b01: dbus_dat_aligned = {lsu_ldat[23:0],8'd0};
      2'b10: dbus_dat_aligned = {lsu_ldat[15:0],16'd0};
      2'b11: dbus_dat_aligned = {lsu_ldat[7:0],24'd0};
    endcase

  // Do appropriate extension for load
  reg [OPTION_OPERAND_WIDTH-1:0] dbus_dat_extended;
  always @(*)
    case({cmd_zext, cmd_length})
      3'b100:  dbus_dat_extended = {24'd0,dbus_dat_aligned[31:24]}; // lbz
      3'b101:  dbus_dat_extended = {16'd0,dbus_dat_aligned[31:16]}; // lhz
      3'b000:  dbus_dat_extended = {{24{dbus_dat_aligned[31]}},
                                    dbus_dat_aligned[31:24]}; // lbs
      3'b001:  dbus_dat_extended = {{16{dbus_dat_aligned[31]}},
                                    dbus_dat_aligned[31:16]}; // lhs
      default: dbus_dat_extended = dbus_dat_aligned;
    endcase

  // ready flag for WB_MUX stored
  //  we need ready flag for l.store for pushing LSU exceptions
  reg lsu_load_rdy_stored, lsu_store_rdy_stored;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      lsu_load_rdy_stored  <= 1'b0;
      lsu_store_rdy_stored <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      lsu_load_rdy_stored  <= 1'b0;
      lsu_store_rdy_stored <= 1'b0;
    end
    else if (padv_wb_i & grant_wb_to_lsu_i) begin
      lsu_load_rdy_stored  <= 1'b0;
      lsu_store_rdy_stored <= 1'b0;
    end
    else begin
      if (~lsu_load_rdy_stored)
        lsu_load_rdy_stored  <= lsu_ack & cmd_load;
      if (~lsu_store_rdy_stored)
        lsu_store_rdy_stored <= lsu_ack & cmd_store;
    end
  end // @clock
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      wb_lsu_rdy_o <= 1'b0;
    end
    else if (padv_wb_i) begin
      if (grant_wb_to_lsu_i)
        wb_lsu_rdy_o <= (lsu_load_rdy_stored ? 1'b1 : wb_lsu_rdy_o);
      else  if (do_rf_wb_i) // another unit is granted with guarantee
        wb_lsu_rdy_o <= 1'b0;
    end
  end // @clock


  // LSU is busy
  //   MAROCCHINO_TODO: potential improvement
  //                    more pipelinization
  assign lsu_busy_o  = op_ls | cmd_ls | lsu_msync_r | msync_busy | tlb_reload_busy | dc_snoop_hit;
  // output assignement (1-clk ahead for WB-latching)
  assign lsu_valid_o = (lsu_load_rdy_stored | lsu_store_rdy_stored) & (~tlb_reload_busy) & (~dc_snoop_hit);


  // output data (latch result of load command)
  reg [OPTION_OPERAND_WIDTH-1:0] lsu_result_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      lsu_result_r <= {OPTION_OPERAND_WIDTH{1'b0}};
    else if (cmd_load & lsu_ack & (~lsu_excepts))
      lsu_result_r <= dbus_dat_extended;
  end // @ clock

  // latch load command result for WB_MUX
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_lsu_result_o <= {OPTION_OPERAND_WIDTH{1'b0}};
    else if (padv_wb_i & grant_wb_to_lsu_i)
      wb_lsu_result_o <= lsu_result_r;
  end // @ clock



  // Data bus mapping for store
  assign lsu_sdat =
    (cmd_length == 2'b00) ? {cmd_rfb[7:0],cmd_rfb[7:0],cmd_rfb[7:0],cmd_rfb[7:0]} : // byte access
    (cmd_length == 2'b01) ? {cmd_rfb[15:0],cmd_rfb[15:0]} : // halfword access
                            cmd_rfb; // word access


  reg [2:0] state;

  // Bus access logic
  localparam [2:0]
    IDLE        = 3'd0,
    READ        = 3'd1,
    WRITE       = 3'd2,
    TLB_RELOAD  = 3'd3,
    DC_REFILL   = 3'd4;

  // Stall until the store buffer is empty
  assign msync_busy = cmd_op_msync & (state != IDLE);
  assign msync_done = cmd_op_msync & (state == IDLE);

  wire store_buffer_ack = (FEATURE_STORE_BUFFER != "NONE") ?
                           store_buffer_write : write_done;

  assign dbus_access = (state == WRITE) |
                       ((state != DC_REFILL) &
                        (cmd_store | tlb_reload_busy | (~dc_access)));

  assign lsu_ack = lsu_excepts ? 1'b0 :
                   (cmd_store | (state == WRITE)) ?
                    ((store_buffer_ack & (~cmd_atomic)) |
                     (write_done       &   cmd_atomic)) :
                    (dbus_access ? dbus_ack : dc_ack);

  assign lsu_ldat = dbus_access ? dbus_dat : dc_ldat;



  assign dbus_adr_o   = dbus_adr;
  assign dbus_dat_o   = dbus_dat;
  assign dbus_burst_o = (state == DC_REFILL) & (~dc_refill_done);

  assign dbus_stall = tlb_reload_busy | lsu_excepts | pipeline_flush_i;

  //
  // Slightly subtle, but if there is an atomic store coming out from the
  // store buffer, and the link has been broken while it was waiting there,
  // the bus access is still performed as a (discarded) read.
  //
  assign dbus_we_o = dbus_we & ((~dbus_atomic) | atomic_reserve);

  assign next_dbus_adr = (OPTION_DCACHE_BLOCK_WIDTH == 5) ?
                         {dbus_adr[31:5], dbus_adr[4:0] + 5'd4} : // 32 byte
                         {dbus_adr[31:4], dbus_adr[3:0] + 4'd4};  // 16 byte


  // state machine
  always @(posedge clk) begin
    // init
    dbus_ack        <= 1'b0;
    write_done      <= 1'b0;
    tlb_reload_ack  <= 1'b0;
    tlb_reload_done <= 1'b0;
    // process
    case (state)
      IDLE: begin
        dbus_req_o  <= 1'b0;
        dbus_we     <= 1'b0;
        dbus_adr    <= 0;
        dbus_bsel_o <= 4'hf;
        dbus_atomic <= 1'b0;
        last_write  <= 1'b0;
        if (~dbus_stall) begin
          if (store_buffer_write | ~store_buffer_empty) begin
            state <= WRITE;
          end
          else if (cmd_ls & (~dc_refill) & dbus_access & (~dbus_ack)) begin
            if (tlb_reload_req) begin
              dbus_req_o <= 1'b1;
              dbus_adr   <= tlb_reload_addr;
              state      <= TLB_RELOAD;
            end
            else if (cmd_load) begin
              dbus_req_o  <= 1'b1;
              dbus_adr    <= dmmu_enable_i ? dmmu_phys_addr : cmd_addr;
              dbus_bsel_o <= dbus_bsel;
              state       <= READ;
            end
          end
          else if (dc_refill_req) begin
            dbus_req_o <= 1'b1;
            dbus_adr   <= dc_adr_match;
            state      <= DC_REFILL;
          end
        end // ~dbus-stall
      end // idle

      DC_REFILL: begin
        dbus_req_o <= 1'b1;
        if (dbus_ack_i) begin
          dbus_adr <= next_dbus_adr;
          if (dc_refill_done) begin
            dbus_req_o <= 1'b0;
            state      <= IDLE;
          end
        end
        // TODO: only abort on snoop-hits to refill address
        if (dbus_err_i | dc_snoop_hit) begin
          dbus_req_o <= 1'b0;
          state      <= IDLE;
        end
      end // dc-refill

      READ: begin
        dbus_ack <= dbus_ack_i;
        dbus_dat <= dbus_dat_i;
        if (dbus_err_i | dbus_ack_i) begin
          dbus_req_o <= 1'b0;
          state      <= IDLE;
        end
      end // read

      WRITE: begin
        dbus_req_o <= 1'b1;
        dbus_we    <= 1'b1;
        //---
        if ((~dbus_req_o) | (dbus_ack_i & (~last_write))) begin
          dbus_bsel_o <= store_buffer_bsel;
          dbus_adr    <= store_buffer_radr;
          dbus_dat    <= store_buffer_dat;
          dbus_atomic <= store_buffer_atomic;
          last_write  <= store_buffer_empty;
        end
        //---
        if (store_buffer_write)
          last_write <= 1'b0;
        //---
        if (dbus_err_i | (dbus_ack_i & last_write)) begin
          dbus_req_o <= 1'b0;
          dbus_we    <= 1'b0;
          if (dbus_err_i | (~store_buffer_write)) begin
            write_done <= 1'b1;
            state      <= IDLE;
          end
        end
      end // write

      TLB_RELOAD: begin
        dbus_adr        <= tlb_reload_addr;
        tlb_reload_data <= dbus_dat_i;
        tlb_reload_ack  <= dbus_ack_i & tlb_reload_req;
        //---
        if (dbus_err_i | (~tlb_reload_req)) begin
          tlb_reload_done <= 1'b1;
          state           <= IDLE;
        end
        //---
        dbus_req_o <= tlb_reload_req;
        if (dbus_ack_i | tlb_reload_ack)
          dbus_req_o <= 1'b0;
      end // tlb-reload

      default: state <= IDLE;
    endcase

    if (rst) begin
      state       <= IDLE;
      dbus_req_o  <= 1'b0;
      dbus_we     <= 1'b0;
      dbus_atomic <= 1'b0;
      last_write  <= 1'b0;
    end
  end // @ clock state machine


  // We have to mask out our snooped bus accesses
  assign snoop_valid = (OPTION_DCACHE_SNOOP != "NONE") &
                       (snoop_en_i & (~((snoop_adr_i == dbus_adr_o) & dbus_ack_i)));


  //-------------------------//
  // Atomic operations logic //
  //-------------------------//

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      atomic_reserve <= 1'b0;
    else if (pipeline_flush_i)
      atomic_reserve <= 1'b0;
    else if ((cmd_swa & write_done) |
             ((~cmd_atomic) & store_buffer_write & (store_buffer_wadr == atomic_addr)) |
             (snoop_valid & (snoop_adr_i == atomic_addr)))
      atomic_reserve <= 1'b0;
    else if (cmd_lwa & cmd_new)
      atomic_reserve <= ~(snoop_valid & (snoop_adr_i == dc_adr_match));
  end // @clock

  always @(posedge clk)
    if (cmd_lwa & cmd_new)
      atomic_addr <= dc_adr_match;

  wire atomic_success = atomic_reserve & (dbus_adr == atomic_addr);

  reg atomic_flag_set;
  reg atomic_flag_clear;

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      atomic_flag_set   <= 1'b0;
      atomic_flag_clear <= 1'b0;
    end
    else if (op_ls | lsu_excepts | pipeline_flush_i) begin
      atomic_flag_set   <= 1'b0;
      atomic_flag_clear <= 1'b0;
    end
    else if (write_done) begin
      atomic_flag_set   <= atomic_success & cmd_swa;
      atomic_flag_clear <= (~atomic_success) & cmd_swa;
    end
  end // @clock

  // atomic flags for WB_MUX
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      wb_atomic_flag_set_o   <= 1'b0;
      wb_atomic_flag_clear_o <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      wb_atomic_flag_set_o   <= 1'b0;
      wb_atomic_flag_clear_o <= 1'b0;
    end
    else if (padv_wb_i) begin
      if (grant_wb_to_lsu_i) begin
        wb_atomic_flag_set_o   <= atomic_flag_set;
        wb_atomic_flag_clear_o <= atomic_flag_clear;
      end
      else begin
        wb_atomic_flag_set_o   <= 1'b0;
        wb_atomic_flag_clear_o <= 1'b0;
      end
    end
  end // @clock


  //--------------------//
  // Store buffer logic //
  //--------------------//
  reg dc_refill_r;
  always @(posedge clk)
    dc_refill_r <= dc_refill;

  always @(posedge clk) begin
    if (rst)
      store_buffer_write_pending <= 1'b0;
    else if (store_buffer_write | pipeline_flush_i)
      store_buffer_write_pending <= 1'b0;
    else if (cmd_store & cmd_new & (~dbus_stall) &
             (store_buffer_full | dc_refill | dc_refill_r | dc_snoop_hit))
      store_buffer_write_pending <= 1'b1;
  end // @ clock

  assign store_buffer_write = ((cmd_store & (cmd_new | tlb_reload_done)) |
                                store_buffer_write_pending) & (~dbus_stall) &
                               (~store_buffer_full) & (~dc_refill) & (~dc_refill_r) & (~dc_snoop_hit);

  assign store_buffer_wadr = dc_adr_match;

generate
if (FEATURE_STORE_BUFFER!="NONE") begin : store_buffer_gen
  assign store_buffer_read = ((state == IDLE) & store_buffer_write) |
                             ((state == IDLE) & (~store_buffer_empty)) |
                             ((state == WRITE) & last_write & store_buffer_write) |
                             ((state == WRITE) & (~last_write) & (store_buffer_write | (~store_buffer_empty)) &
                              (dbus_ack_i | (~dbus_req_o)));

  mor1kx_store_buffer
  #(
    .DEPTH_WIDTH(OPTION_STORE_BUFFER_DEPTH_WIDTH),
    .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH)
  )
  u_store_buffer
  (
    .clk      (clk),
    .rst      (rst),

    .pc_i     (ctrl_epcr_i),
    .adr_i    (store_buffer_wadr),
    .dat_i    (lsu_sdat),
    .bsel_i   (dbus_bsel),
    .atomic_i (cmd_atomic),
    .write_i  (store_buffer_write),

    .pc_o     (store_buffer_epcr_o),
    .adr_o    (store_buffer_radr),
    .dat_o    (store_buffer_dat),
    .bsel_o   (store_buffer_bsel),
    .atomic_o (store_buffer_atomic),
    .read_i   (store_buffer_read),

    .full_o   (store_buffer_full),
    .empty_o  (store_buffer_empty)
  );
end
else begin
  assign store_buffer_epcr_o = ctrl_epcr_i;
  assign store_buffer_radr   = store_buffer_wadr;
  assign store_buffer_dat    = lsu_sdat;
  assign store_buffer_bsel   = dbus_bsel;
  assign store_buffer_empty  = 1'b1;
  assign store_buffer_atomic = cmd_atomic;

  reg store_buffer_full_r;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      store_buffer_full_r <= 1'b0;
    else if (store_buffer_write)
      store_buffer_full_r <= 1'b1;
    else if (write_done)
      store_buffer_full_r <= 1'b0;
  end // @ clock

  assign store_buffer_full = store_buffer_full_r & (~write_done);
end
endgenerate

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      dc_enable_r <= 1'b0;
    else if (dc_enable_i & (~dbus_req_o))
      dc_enable_r <= 1'b1;
    else if ((~dc_enable_i) & (~dc_refill))
      dc_enable_r <= 1'b0;
  end // @ clock

  assign dc_enabled = dc_enable_i & dc_enable_r;


  assign dc_adr = take_op_ls ? lsu_addr : cmd_addr;

  assign dc_adr_match = dmmu_enable_i ?
                      `ifdef SIM_SMPL_SOC
                        dmmu_phys_addr : cmd_addr;
                      `else
                        {dmmu_phys_addr[OPTION_OPERAND_WIDTH-1:2],2'b0} :
                        {cmd_addr[OPTION_OPERAND_WIDTH-1:2],2'b0};
                      `endif

  assign dc_req = cmd_ls & dc_access & (~dbus_stall) &
                  (~(dbus_atomic & dbus_we & (~atomic_reserve)));

  assign dc_refill_allowed = (~(cmd_store | (state == WRITE))) &
                             (~dc_snoop_hit) & (~snoop_valid);

  //-------------------//
  // Instance of cache //
  //-------------------//

generate
  if (OPTION_DCACHE_LIMIT_WIDTH == OPTION_OPERAND_WIDTH) begin
    assign dc_access = cmd_store |
                       (dc_enabled & (~(dmmu_cache_inhibit & dmmu_enable_i)));
  end
  else if (OPTION_DCACHE_LIMIT_WIDTH < OPTION_OPERAND_WIDTH) begin
    assign dc_access = cmd_store |
                       (dc_enabled &
                        (dc_adr_match[OPTION_OPERAND_WIDTH-1:
                                      OPTION_DCACHE_LIMIT_WIDTH] == 0) &
                        (~(dmmu_cache_inhibit & dmmu_enable_i)));
  end
  else begin
    initial begin
      $display("ERROR: OPTION_DCACHE_LIMIT_WIDTH > OPTION_OPERAND_WIDTH");
      $finish();
    end
  end
endgenerate

  assign dc_bsel = dbus_bsel;

  assign dc_we =
    (lsu_store_r & (~lsu_atomic_r) & take_op_ls) |
    (dbus_atomic & dbus_we_o & (~write_done)) |
    (cmd_store & tlb_reload_busy & (~tlb_reload_req));

  mor1kx_dcache
  #(
    .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH),
    .OPTION_DCACHE_BLOCK_WIDTH(OPTION_DCACHE_BLOCK_WIDTH),
    .OPTION_DCACHE_SET_WIDTH(OPTION_DCACHE_SET_WIDTH),
    .OPTION_DCACHE_WAYS(OPTION_DCACHE_WAYS),
    .OPTION_DCACHE_LIMIT_WIDTH(OPTION_DCACHE_LIMIT_WIDTH),
    .OPTION_DCACHE_SNOOP(OPTION_DCACHE_SNOOP)
  )
  u_dcache
  (
    // Outputs
    .refill_o                   (dc_refill),
    .refill_req_o               (dc_refill_req),
    .refill_done_o              (dc_refill_done),
    .cpu_err_o                  (dc_err),
    .cpu_ack_o                  (dc_ack),
    .cpu_dat_o                  (dc_ldat),
    .snoop_hit_o                (dc_snoop_hit),
    .spr_bus_dat_o              (spr_bus_dat_dc_o),
    .spr_bus_ack_o              (spr_bus_ack_dc_o),
    // Inputs
    .clk                        (clk),
    .rst                        (rst),
    .dc_dbus_err_i              (dbus_err),
    .dc_enable_i                (dc_enabled),
    .dc_access_i                (dc_access),
    .cpu_dat_i                  (lsu_sdat),
    .cpu_adr_i                  (dc_adr),
    .cpu_adr_match_i            (dc_adr_match),
    .cpu_req_i                  (dc_req),
    .cpu_we_i                   (dc_we),
    .cpu_bsel_i                 (dc_bsel),
    .refill_allowed             (dc_refill_allowed),
    .wradr_i                    (dbus_adr),
    .wrdat_i                    (dbus_dat_i),
    .we_i                       (dbus_ack_i),
    .snoop_adr_i                (snoop_adr_i[31:0]),
    .snoop_valid_i              (snoop_valid),
    .spr_bus_addr_i             (spr_bus_addr_i[15:0]),
    .spr_bus_we_i               (spr_bus_we_i),
    .spr_bus_stb_i              (spr_bus_stb_i),
    .spr_bus_dat_i              (spr_bus_dat_i)
  );

  //------------------//
  // Instance of DMMU //
  //------------------//

  wire dmmu_enable = dmmu_enable_i & (~pipeline_flush_i); // used for HW TLB reload only

  assign tlb_reload_pagefault_clear = ~cmd_ls;

  mor1kx_dmmu
  #(
    .FEATURE_DMMU_HW_TLB_RELOAD(FEATURE_DMMU_HW_TLB_RELOAD),
    .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH),
    .OPTION_DMMU_SET_WIDTH(OPTION_DMMU_SET_WIDTH),
    .OPTION_DMMU_WAYS(OPTION_DMMU_WAYS)
  )
  u_dmmu
  (
    // clocks and resets
    .clk                              (clk),
    .rst                              (rst),
    // configuration and commands
    .op_store_i                       (cmd_store),
    .op_load_i                        (cmd_load),
    .supervisor_mode_i                (supervisor_mode_i),
    // Input: virtual address
    .virt_addr_i                      (dc_adr),
    .virt_addr_match_i                (cmd_addr),
    // Output: physical address and flags
    .phys_addr_o                      (dmmu_phys_addr),
    .cache_inhibit_o                  (dmmu_cache_inhibit),
    .tlb_miss_o                       (tlb_miss),
    .pagefault_o                      (dmmu_pagefault),
    // HW TLB reload
    .enable_i                         (dmmu_enable),
    .tlb_reload_ack_i                 (tlb_reload_ack),
    .tlb_reload_data_i                (tlb_reload_data),
    .tlb_reload_pagefault_clear_i     (tlb_reload_pagefault_clear),
    .tlb_reload_req_o                 (tlb_reload_req),
    .tlb_reload_busy_o                (tlb_reload_busy),
    .tlb_reload_addr_o                (tlb_reload_addr),
    .tlb_reload_pagefault_o           (tlb_reload_pagefault),
    // SPR bus
    .spr_bus_addr_i                   (spr_bus_addr_i[15:0]),
    .spr_bus_we_i                     (spr_bus_we_i),
    .spr_bus_stb_i                    (spr_bus_stb_i),
    .spr_bus_dat_i                    (spr_bus_dat_i),
    .spr_bus_dat_o                    (spr_bus_dat_dmmu_o),
    .spr_bus_ack_o                    (spr_bus_ack_dmmu_o)
  );

endmodule // mor1kx_lsu_marocchino
