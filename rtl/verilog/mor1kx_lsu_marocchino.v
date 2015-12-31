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

  // Input registers for LSU address calculation stage
  //  # registers for command from DECODE
  reg                            lsu_load_r;
  reg                            lsu_store_r;
  reg                            lsu_atomic_r;
  reg                      [1:0] lsu_length_r;
  reg                            lsu_zext_r;
  //  # registers for operands from DECODE
  reg      [`OR1K_IMM_WIDTH-1:0] lsu_imm16_r; // immediate offset for address computation
  reg [OPTION_OPERAND_WIDTH-1:0] lsu_a_r;     // operand "A" (part of address)
  reg [OPTION_OPERAND_WIDTH-1:0] lsu_b_r;     // operand "B" (value to store)
  //  # operands after frorwarding from WB
  wire [OPTION_OPERAND_WIDTH-1:0] lsu_a;
  wire [OPTION_OPERAND_WIDTH-1:0] lsu_b;
  //  # registers for support forwarding forwarding
  reg                             lsu_fwd_wb_a_r; // use WB result
  reg                             lsu_fwd_wb_b_r; // use WB result


  // Input register for DBUS/DCACHE access stage
  //  # load/store
  reg                            cmd_load_r;  // either atomic or not
  reg                            cmd_lwa_r;   // exactly load linked
  reg                            cmd_store_r; // not (!!!) atomic
  reg                            cmd_swa_r;   // atomic only
  reg                      [1:0] cmd_length;
  reg                            cmd_zext;
  reg [OPTION_OPERAND_WIDTH-1:0] cmd_rfb;  // register file B in (store operand)
  //  # special support for store conditional execution
  reg                            cmd_swa_buffered_r; // l.swa has been put into store buffer
  //  # l.msync
  reg                            cmd_msync_r;


  // DBUS FSM
  //  # DBUS FSM states
  localparam [3:0] IDLE      = 4'b0001,
                   READ      = 4'b0010,
                   WRITE     = 4'b0100,
                   DC_REFILL = 4'b1000;
  //  # DBUS FSM state indicator
  reg [3:0] state;
  //  # DBUS FSM other registers & wires
  reg                               dbus_err;
  reg                               dbus_we;
  wire                              dbus_stall;
  reg                               dbus_atomic;
  wire                              dbus_swa_discard; // reservation is lost, execute empty read
  wire                              dbus_swa_success; // l.swa is successfull
  wire                              dbus_swa_ack;     // complete DBUS trunsaction with l.swa
  reg                               last_write;


  // DMMU
  wire                              dmmu_cache_inhibit;
  wire   [OPTION_OPERAND_WIDTH-1:0] phys_addr_cmd;
  wire   [OPTION_OPERAND_WIDTH-1:0] virt_addr_cmd;
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
  wire                              dc_access;
  wire                              dc_refill_req;
  reg                               dc_refill_allowed; // combinatorial
  wire   [OPTION_OPERAND_WIDTH-1:0] next_refill_adr;
  wire                              dc_refill_last;


  // Store buffer
  wire                              store_buffer_write;
  wire                              store_buffer_read;
  wire                              store_buffer_full;
  wire                              store_buffer_empty;
  wire   [OPTION_OPERAND_WIDTH-1:0] store_buffer_radr;
  wire   [OPTION_OPERAND_WIDTH-1:0] store_buffer_dat;
  wire [OPTION_OPERAND_WIDTH/8-1:0] store_buffer_bsel;
  wire                              store_buffer_atomic;

  // Atomic operations
  reg    [OPTION_OPERAND_WIDTH-1:0] atomic_addr;
  reg                               atomic_reserve;

  // Snoop (for multicore SoC)
  wire                              snoop_event;
  wire                              snoop_hit;

  // Exceptions
  wire                              except_align;
  wire                              except_dbus_err;
  wire                              except_dtlb_miss;
  wire                              except_dpagefault;
  wire                              lsu_excepts; // local use

  // load/store data
  wire   [OPTION_OPERAND_WIDTH-1:0] lsu_ldat; // formated load data
  wire   [OPTION_OPERAND_WIDTH-1:0] lsu_sdat; // formated store data

  // LSU pipe controls
  //  # report on command execution
  wire                              lsu_ack_load;
  wire                              lsu_ack_store;
  wire                              lsu_ack_swa;
  //wire                              lsu_ack;        // combined
  reg                               lsu_ack_load_pending;
  reg                               lsu_ack_store_pending;
  //  # busy of various stages
  wire                              lsu_busy_dc; // DCACHE/DBUS access stage busy
  wire                              lsu_busy_wb; // Result is waiting WB access



  //-------------------//
  // LSU pipe controls //
  //-------------------//

  // Alias for load/store in address computation stage
  wire op_ls      = lsu_load_r | lsu_store_r; // latched load/store

  // signal to take new LSU command (less priority than flushing)
  wire take_op_ls = op_ls & ~snoop_hit & ~(lsu_busy_dc | lsu_busy_wb);

  // exceptions or pipe flushing
  assign dbus_stall = lsu_excepts | pipeline_flush_i;

  // A load/store in DBUS/DCACHE access stage
  wire cmd_ls = cmd_load_r | cmd_store_r | cmd_swa_r | cmd_swa_buffered_r;

  // LSU is busy
  //  # DCACHE/DBUS access stage busy
  assign lsu_busy_dc = cmd_ls | cmd_msync_r | snoop_hit | (state == DC_REFILL);
  //  # Result is waiting WB access
  assign lsu_busy_wb = (lsu_ack_load_pending | lsu_ack_store_pending) & ~grant_wb_to_lsu_i; 
  //   MAROCCHINO_TODO: potential improvement with more pipelinization
  assign lsu_busy_o = op_ls & (lsu_busy_dc | lsu_busy_wb);

  // report on command execution
  //  # load completion
  assign lsu_ack_load  = (((state == READ) & dbus_ack_i) | dc_ack) & cmd_load_r;
  //  # store completion
  assign lsu_ack_store = store_buffer_write & cmd_store_r;
  assign lsu_ack_swa   = dbus_swa_ack & cmd_swa_buffered_r;
  //  # LSU combined ACK
  //assign lsu_ack       = lsu_ack_load | lsu_ack_store | lsu_ack_swa;

  // output assignement (1-clk ahead for WB-latching)
  assign lsu_valid_o = lsu_ack_load_pending | lsu_ack_store_pending;



  //---------------------------//
  // Address computation stage //
  //---------------------------//

  // advance LSU's input latches
  wire padv_lsu_input = padv_decode_i & (dcod_op_lsu_load_i | dcod_op_lsu_store_i);

  // --- latch load/store commands ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      lsu_load_r   <= 1'b0;
      lsu_store_r  <= 1'b0;
      lsu_atomic_r <= 1'b0;
    end
    else if (dbus_stall) begin
      lsu_load_r   <= 1'b0;
      lsu_store_r  <= 1'b0;
      lsu_atomic_r <= 1'b0;
    end
    else if (padv_lsu_input) begin
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
    if (padv_lsu_input) begin
      lsu_imm16_r  <= dcod_imm16_i;
      lsu_length_r <= dcod_lsu_length_i;
      lsu_zext_r   <= dcod_lsu_zext_i;
    end
  end // @clock

  // --- latch forwarding flags ---
  // new LSU input
  reg lsu_new_input_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      lsu_fwd_wb_a_r  <= 1'b0;
      lsu_fwd_wb_b_r  <= 1'b0;
      lsu_new_input_r <= 1'b0;
    end
    else if (dbus_stall) begin
      lsu_fwd_wb_a_r  <= 1'b0;
      lsu_fwd_wb_b_r  <= 1'b0;
      lsu_new_input_r <= 1'b0;
    end
    else if (padv_lsu_input) begin
      lsu_fwd_wb_a_r  <= exe2dec_hazard_a_i;
      lsu_fwd_wb_b_r  <= exe2dec_hazard_b_i; 
      lsu_new_input_r <= 1'b1;
    end
    else if (lsu_new_input_r) begin // complete forwarding from WB
      lsu_fwd_wb_a_r  <= 1'b0;
      lsu_fwd_wb_b_r  <= 1'b0;
      lsu_new_input_r <= 1'b0;
    end
  end // @clock

  // --- opernands ---
  always @(posedge clk) begin
    if (padv_lsu_input) begin
      lsu_a_r <= dcod_rfa_i;
      lsu_b_r <= dcod_rfb_i;
    end
    else if (lsu_new_input_r) begin // complete forwarding from WB
      lsu_a_r <= lsu_a;
      lsu_b_r <= lsu_b;
    end
  end // @clock

  // operands with forwarding from WB
  assign lsu_a = lsu_fwd_wb_a_r ? wb_result_i : lsu_a_r;
  assign lsu_b = lsu_fwd_wb_b_r ? wb_result_i : lsu_b_r;

  // compute address
  wire [OPTION_OPERAND_WIDTH-1:0] virt_addr =
    lsu_a + {{(OPTION_OPERAND_WIDTH-16){lsu_imm16_r[15]}},lsu_imm16_r};


  //---------------------------//
  // DBUS/DCACHE acceess stage //
  //---------------------------//

  // latches for load (either atomic or not) commands
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      cmd_load_r   <= 1'b0;
      cmd_lwa_r    <= 1'b0;
    end
    else if (dbus_stall) begin
      cmd_load_r   <= 1'b0;
      cmd_lwa_r    <= 1'b0;
    end
    else if (take_op_ls) begin
      cmd_load_r   <= lsu_load_r;
      cmd_lwa_r    <= lsu_load_r & lsu_atomic_r;
    end
    else if (lsu_ack_load) begin
      cmd_load_r   <= 1'b0;
      cmd_lwa_r    <= 1'b0;
    end
  end // @clock

  // latche for not conditional store
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      cmd_store_r  <= 1'b0;
    else if (dbus_stall)
      cmd_store_r  <= 1'b0;
    else if (take_op_ls)
      cmd_store_r  <= lsu_store_r & ~lsu_atomic_r;
    else if (lsu_ack_store)
      cmd_store_r  <= 1'b0;
  end // @clock

  // special support for store conditional execution
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      cmd_swa_r          <= 1'b0;
      cmd_swa_buffered_r <= 1'b0;
    end
    else if (dbus_stall) begin
      cmd_swa_r          <= 1'b0;
      cmd_swa_buffered_r <= 1'b0;
    end
    else if (take_op_ls) begin
      cmd_swa_r          <= lsu_store_r & lsu_atomic_r;
      cmd_swa_buffered_r <= 1'b0;
    end
    else if (cmd_swa_r & store_buffer_write) begin
      cmd_swa_r          <= 1'b0;
      cmd_swa_buffered_r <= 1'b1;
    end
    else if (lsu_ack_swa) begin
      cmd_swa_r          <= 1'b0;
      cmd_swa_buffered_r <= 1'b0;
    end
  end // @clock

  // lsu local latched additional parameters
  always @(posedge clk) begin
    if (take_op_ls & ~pipeline_flush_i) begin
      cmd_length <= lsu_length_r;
      cmd_zext   <= lsu_zext_r;
      cmd_rfb    <= lsu_b;
    end
  end // @clock

  // output latched address for exceptions processing
  assign lsu_adr_o = virt_addr_cmd;

  // l.msync to generate msync-stall
  //  # deassert MSYNC
  wire cmd_msync_deassert = cmd_msync_r & (state == IDLE) & // deassert MSYNC
                            ~cmd_ls & store_buffer_empty;   // deassert MSYNC
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      cmd_msync_r <= 1'b0;
    else if (padv_decode_i & dcod_op_msync_i)
      cmd_msync_r <= 1'b1;
    else if (cmd_msync_deassert)
      cmd_msync_r <= 1'b0;
  end // @clock



  //----------------//
  // LSU exceptions //
  //----------------//

  // --- align ---
  wire align_err_word  = |virt_addr[1:0];
  wire align_err_short = virt_addr[0];

  assign except_align = op_ls &
                        (((lsu_length_r == 2'b10) & align_err_word) |
                         ((lsu_length_r == 2'b01) & align_err_short));


  // --- write bus error: clarification just for CTRL ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      store_buffer_err_o <= 1'b0;
    else if (pipeline_flush_i)
      store_buffer_err_o <= 1'b0;
    else if (dbus_err_i & dbus_we_o)
      store_buffer_err_o <= 1'b1;
  end // @ clock
  // --- any bus error ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      dbus_err <= 1'b0;
    else if (pipeline_flush_i)
      dbus_err <= 1'b0;
    else if (dbus_err_i)
      dbus_err <= 1'b1;
  end // @ clock
  // --- combined bus errors ---
  assign except_dbus_err = dbus_err_i | dbus_err;


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
      if (except_align & take_op_ls)
        lsu_except_align_r      <= 1'b1;
      if (except_dbus_err)
        lsu_except_dbus_r       <= 1'b1;
      if (except_dtlb_miss)
        lsu_except_dtlb_miss_r  <= 1'b1;
      if (except_dpagefault)
        lsu_except_dpagefault_r <= 1'b1;
    end
  end // @clock
  
  // output assignement
  assign lsu_excepts_o = lsu_except_dbus_r | lsu_except_align_r | lsu_except_dtlb_miss_r | lsu_except_dpagefault_r;

  // --- combined exception flag (local use) ---
  assign lsu_excepts = except_dbus_err | lsu_except_align_r | except_dtlb_miss | except_dpagefault;

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



  //-----------------//
  // LSU load output //
  //-----------------//

  assign lsu_ldat = dc_access ? dc_dat : dbus_dat_i;

  // Select part of bus for load
  reg [OPTION_OPERAND_WIDTH-1:0] dbus_dat_aligned;
  always @(*) begin
    case(virt_addr_cmd[1:0])
      2'b00: dbus_dat_aligned = lsu_ldat;
      2'b01: dbus_dat_aligned = {lsu_ldat[23:0],8'd0};
      2'b10: dbus_dat_aligned = {lsu_ldat[15:0],16'd0};
      2'b11: dbus_dat_aligned = {lsu_ldat[7:0],24'd0};
    endcase
  end

  // Do appropriate extension for load
  reg [OPTION_OPERAND_WIDTH-1:0] dbus_dat_extended;
  always @(*) begin
    case({cmd_zext, cmd_length})
      3'b100:  dbus_dat_extended = {24'd0,dbus_dat_aligned[31:24]}; // lbz
      3'b101:  dbus_dat_extended = {16'd0,dbus_dat_aligned[31:16]}; // lhz
      3'b000:  dbus_dat_extended = {{24{dbus_dat_aligned[31]}},
                                    dbus_dat_aligned[31:24]}; // lbs
      3'b001:  dbus_dat_extended = {{16{dbus_dat_aligned[31]}},
                                    dbus_dat_aligned[31:16]}; // lhs
      default: dbus_dat_extended = dbus_dat_aligned;
    endcase
  end

  //------------------------------//
  // LSU temporary output storage //
  //------------------------------//

  // pending 'load ready' flag for WB_MUX
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      lsu_ack_load_pending  <= 1'b0;
    else if (dbus_stall | (padv_wb_i & grant_wb_to_lsu_i))
      lsu_ack_load_pending  <= 1'b0;
    else if (~lsu_ack_load_pending)
      lsu_ack_load_pending  <= lsu_ack_load;
  end // @clock

  // pending 'store accepted' flag (we need it for pushing LSU exceptions)
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      lsu_ack_store_pending <= 1'b0;
    else if (dbus_stall | (padv_wb_i & grant_wb_to_lsu_i))
      lsu_ack_store_pending <= 1'b0;
    else if (~lsu_ack_store_pending)
      lsu_ack_store_pending <= lsu_ack_store | lsu_ack_swa;
  end // @clock

  // output data (latch result of load command)
  reg [OPTION_OPERAND_WIDTH-1:0] lsu_result_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      lsu_result_r <= {OPTION_OPERAND_WIDTH{1'b0}};
    else if (dbus_stall)
      lsu_result_r <= lsu_result_r;
    else if (lsu_ack_load)
      lsu_result_r <= dbus_dat_extended;
  end // @ clock

  //------------------------//
  // LSU write-back latches //
  //------------------------//

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      wb_lsu_rdy_o <= 1'b0;
    end
    else if (pipeline_flush_i)
      wb_lsu_rdy_o <= 1'b0;
    else if (padv_wb_i) begin
      if (grant_wb_to_lsu_i)
        wb_lsu_rdy_o <= lsu_ack_load_pending | wb_lsu_rdy_o;
      else  if (do_rf_wb_i) // another unit is granted with guarantee
        wb_lsu_rdy_o <= 1'b0;
    end
  end // @clock

  // latch load command result for WB_MUX
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_lsu_result_o <= {OPTION_OPERAND_WIDTH{1'b0}};
    else if (pipeline_flush_i)
      wb_lsu_result_o <= {OPTION_OPERAND_WIDTH{1'b0}};
    else if (padv_wb_i & grant_wb_to_lsu_i)
      wb_lsu_result_o <= lsu_result_r;
  end // @ clock



  //----------------------------//
  // LSU formatted store output //
  //----------------------------//

  // Big endian bus mapping
  reg [3:0] dbus_bsel;
  always @(*) begin
    case (cmd_length)
      2'b00: // byte access
        case(virt_addr_cmd[1:0])
          2'b00: dbus_bsel = 4'b1000;
          2'b01: dbus_bsel = 4'b0100;
          2'b10: dbus_bsel = 4'b0010;
          2'b11: dbus_bsel = 4'b0001;
        endcase
      2'b01: // halfword access
        case(virt_addr_cmd[1])
          1'b0: dbus_bsel = 4'b1100;
          1'b1: dbus_bsel = 4'b0011;
        endcase
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

  assign dbus_burst_o = (state == DC_REFILL) & ~dc_refill_last;
  //
  // Slightly subtle, but if there is an atomic store coming out from the
  // store buffer, and the link has been broken while it was waiting there,
  // the bus access is still performed as a (discarded) read.
  //
  assign dbus_we_o = dbus_we & ~dbus_swa_discard;


  // re-filll-allowed corresponds to refill-request position in DBUS FSM
  always @(*) begin
    dc_refill_allowed = 1'b0;
    case (state)
      IDLE: begin
        if (store_buffer_write | ~store_buffer_empty) // for re-fill allowed
          dc_refill_allowed = 1'b0;
        else if (dc_refill_req) // it automatically means (l.load & dc-access)
          dc_refill_allowed = 1'b1;
      end
      default:;
    endcase
  end // always

  // state machine
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      state       <= IDLE;
      dbus_adr_o  <= {OPTION_OPERAND_WIDTH{1'b0}};
      dbus_dat_o  <= {OPTION_OPERAND_WIDTH{1'b0}};
      dbus_req_o  <= 1'b0;
      dbus_we     <= 1'b0;
      dbus_bsel_o <= 4'hf;
      dbus_atomic <= 1'b0;
      last_write  <= 1'b0;
    end
    else if (dbus_stall) begin
      state       <= IDLE;
      // MAROCCHINO_TODO: I had to comment the next two
      //                  lines to be able to run Linux
      //                  by U-BOOT
      //dbus_adr_o  <= {OPTION_OPERAND_WIDTH{1'b0}};
      //dbus_dat_o  <= {OPTION_OPERAND_WIDTH{1'b0}};
      dbus_req_o  <= 1'b0;
      dbus_we     <= 1'b0;
      dbus_bsel_o <= 4'hf;
      dbus_atomic <= 1'b0;
      last_write  <= 1'b0;
    end
    else begin
      // process
      case (state)
        IDLE: begin
          dbus_req_o  <= 1'b0;
          dbus_we     <= 1'b0;
          dbus_bsel_o <= 4'hf;
          dbus_atomic <= 1'b0;
          last_write  <= 1'b0;
          if (store_buffer_write | ~store_buffer_empty) begin
            dbus_req_o  <= 1'b1;
            dbus_we     <= 1'b1;
            if (store_buffer_empty) begin   // 1-st write in buffer
              dbus_bsel_o <= dbus_bsel;     // 1-st write in buffer
              dbus_adr_o  <= phys_addr_cmd; // 1-st write in buffer
              dbus_dat_o  <= lsu_sdat;      // 1-st write in buffer
              dbus_atomic <= cmd_swa_r;     // 1-st write in buffer
              last_write  <= 1'b1;          // 1-st write in buffer
            end
            else begin
              dbus_bsel_o <= store_buffer_bsel;   // idle -> write
              dbus_adr_o  <= store_buffer_radr;   // idle -> write
              dbus_dat_o  <= store_buffer_dat;    // idle -> write
              dbus_atomic <= store_buffer_atomic; // idle -> write
              last_write  <= store_buffer_empty;  // idle -> write
            end
            state <= WRITE;
          end
          else if (cmd_load_r & ~dc_access) begin
            dbus_req_o  <= 1'b1;
            dbus_adr_o  <= phys_addr_cmd;
            dbus_bsel_o <= dbus_bsel;
            state       <= READ;
          end
          else if (dc_refill_req) begin
            dbus_req_o <= 1'b1;
            dbus_adr_o <= phys_addr_cmd;
            state      <= DC_REFILL;
          end
        end // idle
  
        DC_REFILL: begin
          dbus_req_o <= 1'b1;
          if (dbus_ack_i) begin
            dbus_adr_o <= next_refill_adr;
            if (dc_refill_last) begin
              dbus_req_o  <= 1'b0;
              dbus_adr_o  <= {OPTION_OPERAND_WIDTH{1'b0}};
              dbus_dat_o  <= {OPTION_OPERAND_WIDTH{1'b0}};
              state       <= IDLE;
            end
          end
          // TODO: only abort on snoop-hits to refill address
          if (snoop_hit) begin
            dbus_req_o  <= 1'b0;
            dbus_adr_o  <= {OPTION_OPERAND_WIDTH{1'b0}};
            dbus_dat_o  <= {OPTION_OPERAND_WIDTH{1'b0}};
            state       <= IDLE;
          end
        end // dc-refill
  
        READ: begin
          if (dbus_ack_i) begin
            dbus_req_o  <= 1'b0;
            dbus_adr_o  <= {OPTION_OPERAND_WIDTH{1'b0}};
            dbus_dat_o  <= {OPTION_OPERAND_WIDTH{1'b0}};
            state       <= IDLE;
          end
        end // read
  
        WRITE: begin
          dbus_req_o  <= 1'b1;
          dbus_we     <= 1'b1;
          //---
          if (dbus_ack_i) begin
            if (last_write) begin
              if (store_buffer_write) begin
                dbus_bsel_o <= dbus_bsel;     // last write overlapped by new store command
                dbus_adr_o  <= phys_addr_cmd; // last write overlapped by new store command
                dbus_dat_o  <= lsu_sdat;      // last write overlapped by new store command
                dbus_atomic <= cmd_swa_r;     // last write overlapped by new store command
                last_write  <= 1'b1;          // last write overlapped by new store command
              end
              else begin
                dbus_req_o  <= 1'b0;
                dbus_we     <= 1'b0;
                dbus_adr_o  <= {OPTION_OPERAND_WIDTH{1'b0}};
                dbus_dat_o  <= {OPTION_OPERAND_WIDTH{1'b0}};
                state       <= IDLE;
              end
            end
            else begin // not last
              dbus_bsel_o <= store_buffer_bsel;   // continous write
              dbus_adr_o  <= store_buffer_radr;   // continous write
              dbus_dat_o  <= store_buffer_dat;    // continous write
              dbus_atomic <= store_buffer_atomic; // continous write
              last_write  <= store_buffer_empty;  // continous write
            end
          end // bus ack
          else if (store_buffer_write) // new store command while waiting bus ack
            last_write <= 1'b0;
        end // write-state
  
        default: begin
          state       <= IDLE;
          dbus_adr_o  <= {OPTION_OPERAND_WIDTH{1'b0}};
          dbus_dat_o  <= {OPTION_OPERAND_WIDTH{1'b0}};
          dbus_req_o  <= 1'b0;
          dbus_we     <= 1'b0;
          dbus_bsel_o <= 4'hf;
          dbus_atomic <= 1'b0;
          last_write  <= 1'b0;
        end
      endcase
    end
  end // @ clock state machine



  //-----------------------//
  // Store buffer instance //
  //-----------------------//

  // "write" and "read" without exception and pipe flushing
  assign store_buffer_write = (cmd_store_r | cmd_swa_r) & ~store_buffer_full & ~snoop_hit;

  assign store_buffer_read = ((state == IDLE)  & (store_buffer_write | ~store_buffer_empty)) |
                             ((state == WRITE) &  last_write &  store_buffer_write) |
                             ((state == WRITE) & ~last_write & ~store_buffer_empty & dbus_ack_i);

  // store buffer controls with exceptions and pipe flushing
  wire store_buffer_we = store_buffer_write & ~dbus_stall;
  wire store_buffer_re = store_buffer_read  & ~dbus_stall;

  // store buffer module
  mor1kx_store_buffer_marocchino
  #(
    .DEPTH_WIDTH          (OPTION_STORE_BUFFER_DEPTH_WIDTH),
    .OPTION_OPERAND_WIDTH (OPTION_OPERAND_WIDTH)
  )
  u_store_buffer
  (
    .clk      (clk),
    .rst      (rst),

    .pc_i     (ctrl_epcr_i), // STORE_BUFFER
    .adr_i    (phys_addr_cmd), // STORE_BUFFER
    .dat_i    (lsu_sdat), // STORE_BUFFER
    .bsel_i   (dbus_bsel), // STORE_BUFFER
    .atomic_i (cmd_swa_r), // STORE_BUFFER
    .write_i  (store_buffer_we), // STORE_BUFFER

    .pc_o     (store_buffer_epcr_o), // STORE_BUFFER
    .adr_o    (store_buffer_radr), // STORE_BUFFER
    .dat_o    (store_buffer_dat), // STORE_BUFFER
    .bsel_o   (store_buffer_bsel), // STORE_BUFFER
    .atomic_o (store_buffer_atomic), // STORE_BUFFER
    .read_i   (store_buffer_re), // STORE_BUFFER

    .full_o   (store_buffer_full), // STORE_BUFFER
    .empty_o  (store_buffer_empty) // STORE_BUFFER
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

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      atomic_reserve <= 1'b0;
      atomic_addr    <= {OPTION_OPERAND_WIDTH{1'b0}};
    end
    else if (dbus_stall | dbus_swa_ack |
             (store_buffer_write & cmd_store_r & (phys_addr_cmd == atomic_addr)) |
             (snoop_event & (snoop_adr_i == atomic_addr))) begin
      atomic_reserve <= 1'b0;
      atomic_addr    <= {OPTION_OPERAND_WIDTH{1'b0}};
    end
    else if (cmd_lwa_r) begin
      if (snoop_event & (snoop_adr_i == phys_addr_cmd)) begin
        atomic_reserve <= 1'b0;
        atomic_addr    <= {OPTION_OPERAND_WIDTH{1'b0}};
      end
      else if (lsu_ack_load) begin
        atomic_reserve <= 1'b1;
        atomic_addr    <= phys_addr_cmd;
      end
    end
  end // @clock

  reg atomic_flag_set;
  reg atomic_flag_clear;

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      atomic_flag_set   <= 1'b0;
      atomic_flag_clear <= 1'b0;
    end
    else if (dbus_stall | (padv_wb_i & grant_wb_to_lsu_i)) begin
      atomic_flag_set   <= 1'b0;
      atomic_flag_clear <= 1'b0;
    end
    else if (dbus_swa_ack) begin
      atomic_flag_set   <=  atomic_reserve;
      atomic_flag_clear <= ~atomic_reserve;
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
        wb_atomic_flag_set_o   <= dbus_swa_success | atomic_flag_set;
        wb_atomic_flag_clear_o <= dbus_swa_fail    | atomic_flag_clear;
      end
      else begin
        wb_atomic_flag_set_o   <= 1'b0;
        wb_atomic_flag_clear_o <= 1'b0;
      end
    end
  end // @clock



  //-------------------//
  // Instance of cache //
  //-------------------//

  wire dc_store_allowed = lsu_ack_store | dbus_swa_success;

  mor1kx_dcache_marocchino
  #(
    .OPTION_OPERAND_WIDTH       (OPTION_OPERAND_WIDTH),
    .OPTION_DCACHE_BLOCK_WIDTH  (OPTION_DCACHE_BLOCK_WIDTH),
    .OPTION_DCACHE_SET_WIDTH    (OPTION_DCACHE_SET_WIDTH),
    .OPTION_DCACHE_WAYS         (OPTION_DCACHE_WAYS),
    .OPTION_DCACHE_LIMIT_WIDTH  (OPTION_DCACHE_LIMIT_WIDTH),
    .OPTION_DCACHE_SNOOP        (OPTION_DCACHE_SNOOP)
  )
  u_dcache
  (
    // clock & reset
    .clk                        (clk), // DCACHE
    .rst                        (rst), // DCACHE
    // pipe controls
    .adv_i                      (take_op_ls), // DCACHE
    // configuration
    .enable_i                   (dc_enable_i), // DCACHE
    // exceptions
    .dbus_stall_i               (dbus_stall), // DCACHE
    // input commands
    //  # for genearel load or store
    .lsu_load_i                 (lsu_load_r), // DCACHE
    .lsu_store_i                (lsu_store_r), // DCACHE
    // Regular operation
    //  # addresses and "DCHACHE inhibit" flag
    .virt_addr_i                (virt_addr), // DCACHE
    .phys_addr_cmd_i            (phys_addr_cmd), // DCACHE
    .dmmu_cache_inhibit_i       (dmmu_cache_inhibit), // DCACHE
    //  # DCACHE regular answer
    .dc_access_o                (dc_access), // DCACHE
    .dc_ack_o                   (dc_ack), // DCACHE
    .dc_dat_o                   (dc_dat), // DCACHE
    //  # STORE format / store data / do|cancel storing
    .dbus_bsel_i                (dbus_bsel), // DCACHE
    .dbus_sdat_i                (lsu_sdat), // DCACHE
    .dc_store_allowed_i         (dc_store_allowed), // DCACHE
    .dbus_swa_discard_i         (dbus_swa_discard), // DCACHE
    // re-fill
    .refill_req_o               (dc_refill_req), // DCACHE
    .refill_allowed_i           (dc_refill_allowed), // DCACHE
    .next_refill_adr_o          (next_refill_adr), // DCACHE
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
    .spr_bus_stb_i              (spr_bus_stb_i), // DCACHE
    .spr_bus_dat_i              (spr_bus_dat_i), // DCACHE
    .spr_bus_dat_o              (spr_bus_dat_dc_o), // DCACHE
    .spr_bus_ack_o              (spr_bus_ack_dc_o) // DCACHE
  );



  //------------------//
  // Instance of DMMU //
  //------------------//

  mor1kx_dmmu_marocchino
  #(
    .FEATURE_DMMU_HW_TLB_RELOAD (FEATURE_DMMU_HW_TLB_RELOAD),
    .OPTION_OPERAND_WIDTH       (OPTION_OPERAND_WIDTH),
    .OPTION_DMMU_SET_WIDTH      (OPTION_DMMU_SET_WIDTH),
    .OPTION_DMMU_WAYS           (OPTION_DMMU_WAYS)
  )
  u_dmmu
  (
    // clocks and resets
    .clk                              (clk), // DMMU
    .rst                              (rst), // DMMU
    // pipe controls
    .adv_i                            (take_op_ls), // DMMU
    .pipeline_flush_i                 (pipeline_flush_i), // DMMU
    // configuration and commands
    .enable_i                         (dmmu_enable_i), // DMMU
    .supervisor_mode_i                (supervisor_mode_i), // DMMU
    .cmd_store_i                      (cmd_store_r | cmd_swa_r | cmd_swa_buffered_r), // DMMU
    .cmd_load_i                       (cmd_load_r), // DMMU
    // address translation
    .virt_addr_i                      (virt_addr), // DMMU
    .virt_addr_cmd_o                  (virt_addr_cmd), // DMMU
    .phys_addr_cmd_o                  (phys_addr_cmd), // DMMU
    // translation flags
    .cache_inhibit_o                  (dmmu_cache_inhibit), // DMMU
    .tlb_miss_o                       (except_dtlb_miss), // DMMU
    .pagefault_o                      (except_dpagefault), // DMMU
    // HW TLB reload face.  MAROCCHINO_TODO: not implemented
    .tlb_reload_ack_i                 (1'b0), // DMMU
    .tlb_reload_data_i                ({OPTION_OPERAND_WIDTH{1'b0}}), // DMMU
    .tlb_reload_pagefault_clear_i     (1'b0), // DMMU
    .tlb_reload_req_o                 (), // DMMU
    .tlb_reload_busy_o                (), // DMMU
    .tlb_reload_addr_o                (), // DMMU
    .tlb_reload_pagefault_o           (), // DMMU
    // SPR bus
    .spr_bus_addr_i                   (spr_bus_addr_i[15:0]), // DMMU
    .spr_bus_we_i                     (spr_bus_we_i), // DMMU
    .spr_bus_stb_i                    (spr_bus_stb_i), // DMMU
    .spr_bus_dat_i                    (spr_bus_dat_i), // DMMU
    .spr_bus_dat_o                    (spr_bus_dat_dmmu_o), // DMMU
    .spr_bus_ack_o                    (spr_bus_ack_dmmu_o) // DMMU
  );

endmodule // mor1kx_lsu_marocchino
