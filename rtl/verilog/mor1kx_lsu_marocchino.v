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
  input                                 cpu_clk,
  input                                 cpu_rst,
  // Pipeline controls
  input                                 pipeline_flush_i,
  input                                 padv_wrbk_i,
  input                                 grant_wrbk_to_lsu_i,
  // configuration
  input                                 dc_enable_i,
  input                                 dmmu_enable_i,
  input                                 supervisor_mode_i,
  // Input from RSRVS
  input                                 exec_op_lsu_any_i,
  input                                 exec_op_lsu_load_i,
  input                                 exec_op_lsu_store_i,
  input                                 exec_op_msync_i,
  input                                 exec_op_lsu_atomic_i,
  input                           [1:0] exec_lsu_length_i,
  input                                 exec_lsu_zext_i,
  input           [`OR1K_IMM_WIDTH-1:0] exec_lsu_imm16_i, // immediate offset for address computation
  input                                 exec_lsu_delay_slot_i, // for store buffer EPCR computation
  input      [OPTION_OPERAND_WIDTH-1:0] exec_lsu_pc_i, // for store buffer EPCR computation
  input      [OPTION_OPERAND_WIDTH-1:0] exec_lsu_a1_i,   // operand "A" (part of address)
  input      [OPTION_OPERAND_WIDTH-1:0] exec_lsu_b1_i,   // operand "B" (value to store)
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
  output reg                            dbus_lwa_cmd_o, // atomic load
  output reg                            dbus_stna_cmd_o, // none-atomic store
  output reg                            dbus_swa_cmd_o, // atomic store
  output reg                            dbus_burst_o,
  input                                 dbus_err_i,
  input                                 dbus_ack_i,
  input      [OPTION_OPERAND_WIDTH-1:0] dbus_dat_i,
  input                                 dbus_burst_last_i,
  // Other connections for lwa/swa support
  input                                 dbus_atomic_flg_i,
  // Cache sync for multi-core environment
  input                          [31:0] snoop_adr_i,
  input                                 snoop_en_i,
  // Pipe control output flags
  output                                lsu_taking_op_o,
  output                                lsu_valid_o, // result ready or exceptions
  // Imprecise exception (with appropriate PC) came via the store buffer
  output reg [OPTION_OPERAND_WIDTH-1:0] sbuf_eear_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] sbuf_epcr_o,
  output reg                            sbuf_err_o,
  //  Pre-WriteBack "an exception" flag
  output                                exec_an_except_lsu_o,
  // WriteBack load  result
  output reg [OPTION_OPERAND_WIDTH-1:0] wrbk_lsu_result_o,
  // Atomic operation flag set/clear logic
  output reg                            wrbk_atomic_flag_set_o,
  output reg                            wrbk_atomic_flag_clear_o,
  // Exceptions & errors
  output reg                            wrbk_except_dbus_err_o,
  output reg                            wrbk_except_dpagefault_o,
  output reg                            wrbk_except_dtlb_miss_o,
  output reg                            wrbk_except_dbus_align_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] wrbk_lsu_except_addr_o
);


  // short names for local use
  localparam LSUOOW = OPTION_OPERAND_WIDTH;



  // output registers of DMMU stage
  reg               s1o_op_lsu_load;
  reg               s1o_op_lsu_store;   // any kind: atomic or regular
  reg               s1o_op_lsu_atomic;
  reg               s1o_op_msync;
  reg               s1o_op_lsu_ls;
  reg  [LSUOOW-1:0] s1o_virt_addr;
  reg  [LSUOOW-1:0] s1o_lsu_b1;
  reg  [LSUOOW-1:0] s1o_sbuf_epcr;       // for store buffer EPCR computation
  reg         [1:0] s1o_lsu_length;
  reg               s1o_lsu_zext;
  // IMMU's super-cache statuses
  wire              s1o_dmmu_rdy;
  wire              s1o_dmmu_upd;
  /* HW reload TLB related (MAROCCHINO_TODO : not implemented yet)
  wire              tlb_reload_req;
  wire              tlb_reload_busy;
  wire [LSUOOW-1:0] tlb_reload_addr;
  wire              tlb_reload_pagefault;
  reg               tlb_reload_ack;
  reg  [LSUOOW-1:0] tlb_reload_data;
  wire              tlb_reload_pagefault_clear;
  reg               tlb_reload_done; */


  // Register na wires for stage #2: DBUS access / DCACHE check

  //  # any kind of command has been taken
  reg               s2o_op_lsu_store;

  //  # load command
  reg               s2o_lwa_req;   // exactly atomic load
  reg         [1:0] s2o_length;
  reg               s2o_zext;
  //  # load processing
  //    ## cachable area
  wire              s2t_dc_ack_read;
  reg               s2o_dc_ack_read;
  wire [LSUOOW-1:0] s2t_dc_dat;
  reg  [LSUOOW-1:0] s2o_dc_dat;
  wire              s2t_dc_refill_req;
  reg               s2o_dc_refill_req;
  wire              dc_refill_allowed;
  wire              dc_refill_first;
  //    ## none cachable area
  wire              s2t_dbus_read_req;
  reg               s2o_dbus_read_req;
  wire              dbus_load_ack;
  wire              dbus_load_err;
  reg  [LSUOOW-1:0] s2o_dbus_dat;

  //  # store
  reg               s2o_stna_req; // not atomic store
  reg               s2o_swa_req;  // atomic only
  //  # auxiliaries
  //  # DBUS "bsel" and formatted data to store
  reg         [3:0] s2o_bsel;
  reg  [LSUOOW-1:0] s2o_sdat;     // register file B in (store operand)
  wire              dbus_swa_ack; // complete DBUS trunsaction with l.swa
  //    ## combined store ACK
  wire              s3t_store_ack;

  //  # snoop-invalidation
  wire              dc_snoop2refill; // snoop-inv -> restore re-fill
  wire              dc_snoop2write;  // snoop-inv -> restore write

  //  # combined DBUS-load/SBUFF-store ACK
  reg               s3o_ls_ack;

  //    ## registers for store buffer EPCR computation
  reg  [LSUOOW-1:0] s2o_epcr;

  //  # latched virtual and physical addresses
  reg  [LSUOOW-1:0] s2o_virt_addr;
  reg  [LSUOOW-1:0] s2o_phys_addr;

  wire              lsu_s2_rdy;       // operation complete or an exception
  reg               wrbk_lsu_miss_r;  // pending registers are busy


  // DBUS FSM
  //  # DBUS FSM states
  localparam [6:0] DBUS_IDLE      = 7'b0000001, // 0
                   DMEM_REQ       = 7'b0000010, // 1
                   DBUS_READ      = 7'b0000100, // 2
                   DBUS_TO_REFILL = 7'b0001000, // 3
                   DBUS_DC_REFILL = 7'b0010000, // 4
                   DBUS_SBUF_READ = 7'b0100000, // 5
                   DBUS_WRITE     = 7'b1000000; // 6
  //  # DBUS FSM state indicator
  reg        [6:0] dbus_state;
  //  # particular states
  wire             dbus_idle_state    = dbus_state[0];
  wire             dmem_req_state     = dbus_state[1];
  wire             dbus_read_state    = dbus_state[2];
  assign           dc_refill_allowed  = dbus_state[3];
  wire             dc_refill_state    = dbus_state[4];
  wire             sbuf_read_state    = dbus_state[5];
//wire             dbus_write_state   = dbus_state[6];


  // Store buffer
  wire              sbuf_write; // without exceptions and pipeline-flush
  wire              sbuf_we;    // with exceptions and pipeline-flush
  // ---
  wire              sbuf_full;
  wire              sbuf_empty;
  wire [LSUOOW-1:0] sbuf_epcr;
  wire [LSUOOW-1:0] sbuf_virt_addr;
  wire [LSUOOW-1:0] sbuf_phys_addr;
  wire [LSUOOW-1:0] sbuf_dat;
  wire        [3:0] sbuf_bsel;


  // Snoop (for multicore SoC)
  wire              s2o_snoop_proc;


  // Exceptions detected on DCACHE/DBUS access stage
  //  # latched address convertion exceptions
  reg               s2o_tlb_miss;
  reg               s2o_pagefault;
  reg               s2o_align;
  // # combination of align/tlb/pagefault
  wire              s2t_excepts_addr;
  reg               s2o_excepts_addr;
  // # DBUS error not related to STORE_BUFFER
  wire              s3t_dbus_err_nsbuf;
  reg               s2o_dbus_err_nsbuf;
  // # combined of address + DBUS error not related to STORE_BUFFER
  reg               s2o_excepts_any;

  // Flushing logic provides continuous clean up output
  // from pipeline-flush till transaction (read/re-fill) completion
  reg               flush_r;
  wire              flush_by_ctrl;


  //*******************//
  // LSU pipe controls //
  //*******************//


  // LSU pipe controls
  //  ## per stage busy signals
  wire   lsu_s2_busy = s2o_dc_refill_req | s2o_dbus_read_req | // stage #2 is busy
                       s2o_op_lsu_store                      | // stage #2 is busy
                       (lsu_s2_rdy & wrbk_lsu_miss_r)        | // stage #2 is busy
                       s2o_excepts_any   | s2o_snoop_proc;     // stage #2 is busy
  //  ---
  wire   lsu_s1_busy = (s1o_op_lsu_ls & lsu_s2_busy) |  // stage #1 is busy
                       s1o_op_msync | s1o_dmmu_upd;     // stage #1 is busy
  //  ## per stage advance signals
  wire   lsu_s1_adv  = exec_op_lsu_any_i            & (~lsu_s1_busy);
  wire   lsu_s2_adv  = s1o_op_lsu_ls & s1o_dmmu_rdy & (~lsu_s2_busy);
  wire   lsu_s3_adv  = lsu_s2_rdy                   & (~wrbk_lsu_miss_r);
  //  ## to LSU_RSRVS
  assign lsu_taking_op_o = lsu_s1_adv;


  // DBUS read completion
  assign dbus_load_ack = (dbus_read_state | dc_refill_first) & dbus_ack_i;
  assign dbus_load_err = (dbus_read_state | dc_refill_state) & dbus_err_i;

  // Combined store ACK
  //  # for command clean up
  assign s3t_store_ack    = sbuf_write |  dbus_swa_ack;
  //  # for DCAHCE
  wire   dc_store_allowed = sbuf_write;
  // !!! (dc_store_cancel == mor1kx_dcache_marocchino.dc_cancel) !!!
  //wire   dc_store_cancel  = (pipeline_flush_i | s2o_excepts_addr); // cancel write-hit in DCACHE


  // DBUS error not related to store buffer
  // note: l.swa goes around store buffer
  assign s3t_dbus_err_nsbuf = dbus_load_err | (dbus_swa_cmd_o & dbus_err_i);


  //-----------------------------------------------------------------//
  // Flushing from pipeline-flush-i till DBUS transaction completion //
  //-----------------------------------------------------------------//

  assign flush_by_ctrl = pipeline_flush_i | flush_r;


  //--------------------//
  // SPR access support //
  //--------------------//

  //   For MAROCCHINO SPR access means that pipeline is stalled till ACK.
  // So, no padv-*. We only delay SPR access command till DBUS transaction
  // completion.

  wire spr_bus_stb_lsu = spr_bus_stb_i & dbus_idle_state; // SPR access


  /*********************************/
  /* Stage #1: address computation */
  /*********************************/

  // compute virtual address
  wire [LSUOOW-1:0] s1t_virt_addr = exec_lsu_a1_i + {{(LSUOOW-16){exec_lsu_imm16_i[15]}},exec_lsu_imm16_i};

  // store buffer EPCR computation: delay-slot ? (pc-4) : pc
  wire [LSUOOW-1:0] s1t_sbuf_epcr = exec_lsu_pc_i + {{(LSUOOW-2){exec_lsu_delay_slot_i}},2'b00};


  // load / store and "new command is in stage #1" flag
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i) begin
      s1o_op_lsu_store  <= 1'b0;  // reset / flush
      s1o_op_lsu_load   <= 1'b0;  // reset / flush
      s1o_op_lsu_atomic <= 1'b0;  // reset / flush
      s1o_op_lsu_ls     <= 1'b0;  // reset / flush
    end
    else if (lsu_s1_adv) begin // rise "new load command is in stage #1" flag
      s1o_op_lsu_store  <= exec_op_lsu_store_i; // advance stage #1
      s1o_op_lsu_load   <= exec_op_lsu_load_i; // advance stage #1
      s1o_op_lsu_atomic <= exec_op_lsu_atomic_i; // advance stage #1
      s1o_op_lsu_ls     <= (exec_op_lsu_load_i | exec_op_lsu_store_i); // advance stage #1
    end
    else if (lsu_s2_adv) begin   // drop "new load command is in stage #1" flag
      s1o_op_lsu_store  <= 1'b0; // advance stage #2 only
      s1o_op_lsu_load   <= 1'b0; // advance stage #2 only
      s1o_op_lsu_atomic <= 1'b0; // advance stage #2 only
      s1o_op_lsu_ls     <= 1'b0; // advance stage #2 only
    end
  end // @cpu-clk

  // l.msync is express (and 1-clock length)
  always @(posedge cpu_clk) begin
    if (cpu_rst)                           // ! no flushing for l.msync
      s1o_op_msync <= 1'b0;
    else if (lsu_s1_adv)                   // latch l.msync from LSU-RSRVS
      s1o_op_msync <= exec_op_msync_i;
    else if (dbus_idle_state & sbuf_empty) // de-assert msync
      s1o_op_msync <= 1'b0;                // de-assert msync
  end // @cpu-clk

  // load/store attributes
  always @(posedge cpu_clk) begin
    if (lsu_s1_adv) begin // latch data from LSU-RSRVS without l.msync
      s1o_virt_addr  <= s1t_virt_addr;
      s1o_lsu_b1     <= exec_lsu_b1_i;
      s1o_sbuf_epcr  <= s1t_sbuf_epcr;
      s1o_lsu_length <= exec_lsu_length_i;
      s1o_lsu_zext   <= exec_lsu_zext_i;
    end
  end // @cpu-clk


  // --- Big endian bus mapping ---
  reg [3:0] s2t_bsel;
  // ---
  always @(s1o_lsu_length or s1o_virt_addr[1:0]) begin
    // synthesis parallel_case
    case (s1o_lsu_length)
      2'b00: // byte access
      begin
        // synthesis parallel_case
        case( s1o_virt_addr[1:0])
          2'b00: s2t_bsel = 4'b1000;
          2'b01: s2t_bsel = 4'b0100;
          2'b10: s2t_bsel = 4'b0010;
          2'b11: s2t_bsel = 4'b0001;
        endcase
      end
      2'b01: // halfword access
      begin
        // synthesis parallel_case
        case(s1o_virt_addr[1])
          1'b0: s2t_bsel = 4'b1100;
          1'b1: s2t_bsel = 4'b0011;
        endcase
      end
      2'b10,
      2'b11: s2t_bsel = 4'b1111;
    endcase
  end

  // --- Data bus mapping for store ---
  wire [LSUOOW-1:0] s2t_sdat =
    (s1o_lsu_length == 2'b00) ? {s1o_lsu_b1[7:0],s1o_lsu_b1[7:0],s1o_lsu_b1[7:0],s1o_lsu_b1[7:0]} : // byte access
    (s1o_lsu_length == 2'b01) ? {s1o_lsu_b1[15:0],s1o_lsu_b1[15:0]} : // halfword access
                                s1o_lsu_b1; // word access

  // --- align error detection ---
  wire s2t_align = s1o_op_lsu_ls &                                        // Align Exception: detection enabled
                   (((s1o_lsu_length == 2'b10) & (|s1o_virt_addr[1:0])) | // Align Exception: wrong word align
                    ((s1o_lsu_length == 2'b01) & s1o_virt_addr[0]));      // Align Exception: wrong short align


  // address conversion result
  wire [LSUOOW-1:0] s2t_phys_addr;
  wire              s2t_cache_inhibit;
  wire              s2t_tlb_miss;
  wire              s2t_pagefault;

  //------------------//
  // Instance of DMMU //
  //------------------//

  mor1kx_dmmu_marocchino
  #(
    .FEATURE_DMMU_HW_TLB_RELOAD       (FEATURE_DMMU_HW_TLB_RELOAD), // DMMU
    .OPTION_OPERAND_WIDTH             (OPTION_OPERAND_WIDTH), // DMMU
    .OPTION_DMMU_SET_WIDTH            (OPTION_DMMU_SET_WIDTH), // DMMU
    .OPTION_DMMU_WAYS                 (OPTION_DMMU_WAYS), // DMMU
    .OPTION_DCACHE_LIMIT_WIDTH        (OPTION_DCACHE_LIMIT_WIDTH), // DMMU
    .OPTION_DMMU_CLEAR_ON_INIT        (OPTION_DMMU_CLEAR_ON_INIT) // DMMU
  )
  u_dmmu
  (
    // clocks and resets
    .cpu_clk                          (cpu_clk), // DMMU
    .cpu_rst                          (cpu_rst), // DMMU
    // pipe controls
    .lsu_s1_adv_i                     (lsu_s1_adv), // DMMU
    .pipeline_flush_i                 (pipeline_flush_i), // DMMU
    .s1o_dmmu_rdy_o                   (s1o_dmmu_rdy), // DMMU
    .s1o_dmmu_upd_o                   (s1o_dmmu_upd), // DMMU
    // configuration and commands
    .dmmu_enable_i                    (dmmu_enable_i), // DMMU
    .supervisor_mode_i                (supervisor_mode_i), // DMMU
    .s1o_op_lsu_store_i               (s1o_op_lsu_store), // DMMU
    .s1o_op_lsu_load_i                (s1o_op_lsu_load), // DMMU
    .s1o_op_msync_i                   (s1o_op_msync), // DMMU
    // address translation
    .virt_addr_idx_i                  (s1t_virt_addr), // DMMU
    .virt_addr_s1o_i                  (s1o_virt_addr), // DMMU
    .phys_addr_o                      (s2t_phys_addr), // DMMU
    // translation flags
    .cache_inhibit_o                  (s2t_cache_inhibit), // DMMU
    .tlb_miss_o                       (s2t_tlb_miss), // DMMU
    .pagefault_o                      (s2t_pagefault), // DMMU
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

  // Combination of align/tlb/pagefault
  assign s2t_excepts_addr = s2t_tlb_miss | s2t_pagefault | s2t_align;


  //-------------------//
  // Instance of cache //
  //-------------------//

  // Condition to restore re-fill state in DCACHE
  // after snoop invalidation completion.
  //  Pay attention that if re-fiil once initiated
  // it could not be interrupted by pipe flushing
  assign dc_snoop2refill = dc_refill_allowed | dc_refill_state;

  // Condition to restore write state in DCACHE
  // after snoop invalidation completion.
  //  !!! keep consistency with s2o_stna_req logic !!!
  assign dc_snoop2write = s2o_stna_req;

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
    .cpu_clk                    (cpu_clk), // DCACHE
    .cpu_rst                    (cpu_rst), // DCACHE
    // pipe controls
    .lsu_s1_adv_i               (lsu_s1_adv), // DACHE
    .lsu_s2_adv_i               (lsu_s2_adv), // DACHE
    .pipeline_flush_i           (pipeline_flush_i), // DCACHE
    // configuration
    .dc_enable_i                (dc_enable_i), // DCACHE
    // exceptions
    .s2o_excepts_addr_i         (s2o_excepts_addr), // DCACHE
    .dbus_err_i                 (dbus_err_i), // DCACHE
    // Regular operation
    //  # addresses and "DCHACHE inhibit" flag
    .virt_addr_idx_i            (s1t_virt_addr), // DCACHE
    .virt_addr_s1o_i            (s1o_virt_addr), // DCACHE
    .virt_addr_s2o_i            (s2o_virt_addr), // DCACHE
    .phys_addr_s2t_i            (s2t_phys_addr), // DCACHE
    .dmmu_cache_inhibit_i       (s2t_cache_inhibit), // DCACHE
    //  # DCACHE regular answer
    .s1o_op_lsu_load_i          (s1o_op_lsu_load), // DCACHE
    .dc_ack_read_o              (s2t_dc_ack_read), // DCACHE
    .dc_dat_o                   (s2t_dc_dat), // DCACHE
    //  # STORE format / store data / do|cancel storing
    .s1o_op_lsu_store_i         (s1o_op_lsu_store), // DCACHE
    .dbus_bsel_i                (s2o_bsel), // DCACHE
    .dbus_sdat_i                (s2o_sdat), // DCACHE
    .dc_dat_s2o_i               (s2o_dc_dat), // DCACHE
    .dc_store_allowed_i         (dc_store_allowed), // DCACHE
    // !!! (dc_store_cancel == mor1kx_dcache_marocchino.dc_cancel) !!!
    //.dc_store_cancel_i          (dc_store_cancel), // DCACHE
    //  # Atomics
    .s1o_op_lsu_atomic_i        (s1o_op_lsu_atomic), // DCACHE
    // re-fill
    .dc_refill_req_o            (s2t_dc_refill_req), // DCACHE
    .dc_refill_allowed_i        (dc_refill_allowed), // DCACHE
    .refill_first_o             (dc_refill_first), // DCACHE
    .phys_addr_s2o_i            (s2o_phys_addr), // DCACHE
    .dbus_dat_i                 (dbus_dat_i), // DCACHE
    .dbus_ack_i                 (dbus_ack_i), // DCACHE
    .dbus_burst_last_i          (dbus_burst_last_i), // DCACHE
    // DBUS read request
    .dbus_read_req_o            (s2t_dbus_read_req), // DCACHE
    // SNOOP
    .snoop_adr_i                (snoop_adr_i), // DCACHE
    .snoop_en_i                 (snoop_en_i), // DCACHE
    .s2o_snoop_proc_o           (s2o_snoop_proc), // DCACHE
    .dc_snoop2refill_i          (dc_snoop2refill), // DCACHE
    .dc_snoop2write_i           (dc_snoop2write), // DCACHE
    // SPR interface
    .spr_bus_addr_i             (spr_bus_addr_i[15:0]), // DCACHE
    .spr_bus_we_i               (spr_bus_we_i), // DCACHE
    .spr_bus_stb_i              (spr_bus_stb_lsu), // DCACHE
    .spr_bus_dat_i              (spr_bus_dat_i), // DCACHE
    .spr_bus_dat_o              (spr_bus_dat_dc_o), // DCACHE
    .spr_bus_ack_o              (spr_bus_ack_dc_o) // DCACHE
  );


  /*****************************************/
  /* Stage #2: DBUS acceess / DCACHE check */
  /*****************************************/

  //----------------------------//
  // STORE_BUFF error exception //
  //----------------------------//

  // --- bus error during bus access from store buffer ---
  //  ## pay attention that l.swa is executed around of
  //     store buffer, so we don't take it into accaunt here.
  wire sbuf_err = dbus_stna_cmd_o & dbus_err_i; // to force empty STORE_BUFFER
  // ---
  always @(posedge cpu_clk) begin
    if (flush_by_ctrl) // reset store buffer DBUS error
      sbuf_err_o <= 1'b0;
    else if (sbuf_err)          // rise store buffer DBUS error
      sbuf_err_o <= 1'b1;
  end // @ clock

  //----------//
  // DBUS FSM //
  //----------//

  // DBUS state machine: switching
  always @(posedge cpu_clk) begin
    if (cpu_rst) begin
      dbus_req_o      <= 1'b0;      // DBUS_FSM reset
      dbus_lwa_cmd_o  <= 1'b0;      // DBUS_FSM reset
      dbus_stna_cmd_o <= 1'b0;      // DBUS_FSM reset
      dbus_swa_cmd_o  <= 1'b0;      // DBUS_FSM reset
      dbus_burst_o    <= 1'b0;      // DBUS_FSM reset
      dbus_state      <= DBUS_IDLE; // DBUS_FSM reset
    end
    else begin
      // synthesis parallel_case
      case (dbus_state)
        DBUS_IDLE: begin
          if (pipeline_flush_i)           // DBUS_FSM: keep idling
            dbus_state <= DBUS_IDLE;      // DBUS_FSM: keep idling
          else if (~sbuf_empty)           // DBUS_FSM: idle -> dbus-sbuf-read
            dbus_state <= DBUS_SBUF_READ; // DBUS_FSM: idle -> dbus-sbuf-read
          else if (lsu_s2_adv)            // DBUS_FSM: idle -> dmem req
            dbus_state <= DMEM_REQ;       // DBUS_FSM: idle -> dmem req
        end // idle

        DMEM_REQ: begin
          if (pipeline_flush_i) begin       // dmem req
            dbus_state <= DBUS_IDLE;        // dmem req: pipe flush
          end
          else if (~sbuf_empty) begin       // dmem req
            dbus_state <= DBUS_SBUF_READ;   // dmem req -> dbus-sbuf-read
          end
          else if (s2o_excepts_addr) begin  // dmem req
            dbus_state <= DBUS_IDLE;        // dmem req: address conversion an exception
          end
          else if (s2o_swa_req) begin
            dbus_req_o     <= ~dbus_req_o;   // dmem req -> write for l.swa
            dbus_swa_cmd_o <= 1'b1;          // dmem req -> write for l.swa
            dbus_state     <= DBUS_WRITE;    // dmem req -> write for l.swa
          end
          else if (s2o_dc_refill_req) begin // dmem-req
            dbus_req_o   <= ~dbus_req_o;    // dmem-req -> to-re-fill
            dbus_burst_o <= 1'b1;           // dmem req -> to-re-fill
            dbus_state   <= DBUS_TO_REFILL; // dmem-req -> to-re-fill
          end
          else if (s2o_dbus_read_req) begin // dmem-req
            dbus_req_o     <= ~dbus_req_o;  // dmem-req -> dbus-read
            dbus_lwa_cmd_o <= s2o_lwa_req;  // dmem-req -> dbus-read
            dbus_state     <= DBUS_READ;    // dmem-req -> dbus-read
          end
          else if (~lsu_s2_adv) begin       // dmem-req: no new memory request MAROCCHINO_TODO: redundancy ??
            dbus_state <= DBUS_IDLE;        // dmem-req: no new memory request
          end
        end // dmem-req

        DBUS_READ: begin
          if (dbus_err_i | dbus_ack_i) begin  // dbus-read
            dbus_lwa_cmd_o <= 1'b0;           // dbus-read: eror OR complete
            dbus_state     <= DBUS_IDLE;      // dbus-read: eror OR complete
          end
        end // dbus-read

        DBUS_TO_REFILL: begin
          dbus_state <= DBUS_DC_REFILL;  // to-re-fill -> dcache-re-fill
        end // to-re-fill

        DBUS_DC_REFILL: begin
          if (dbus_err_i | (dbus_ack_i & dbus_burst_last_i)) begin  // dcache-re-fill
            dbus_burst_o <= 1'b0;      // dcache-re-fill: DBUS error / last re-fill
            dbus_state   <= DBUS_IDLE; // dcache-re-fill: DBUS error / last re-fill
          end
        end // dc-refill

        DBUS_SBUF_READ: begin
          dbus_req_o      <= ~dbus_req_o; // dbus-sbuf-read -> write
          dbus_stna_cmd_o <= 1'b1;        // dbus-sbuf-read -> write
          dbus_state      <= DBUS_WRITE;  // dbus-sbuf-read -> write
        end // dbus-sbuf-red

        DBUS_WRITE: begin
          // drop store commands
          if (dbus_err_i | dbus_ack_i) begin
            dbus_stna_cmd_o <= 1'b0;    // dbus-write: error OR complete
            dbus_swa_cmd_o  <= 1'b0;    // dbus-write: error OR complete
          end
          // next state
          if (dbus_err_i) begin         // dbus-write
            dbus_state <= DBUS_IDLE;    // dbus-write: DBUS error
          end
          else if (dbus_ack_i) begin
            dbus_state <= sbuf_empty ? DMEM_REQ : DBUS_SBUF_READ; // DBUS: write complete
          end
        end // dbus-write

        default:;
      endcase
    end
  end // @ clock: DBUS_FSM

  // DBUS state machine: control signals
  always @(posedge cpu_clk) begin
    // synthesis parallel_case
    case (dbus_state)
      DMEM_REQ: begin
        if (pipeline_flush_i | (~sbuf_empty) | s2o_excepts_addr) begin // dmem-req
        end
        else if (s2o_swa_req) begin
          dbus_bsel_o   <= s2o_bsel;      // dmem req -> write for l.swa
          dbus_adr_o    <= s2o_phys_addr; // dmem req -> write for l.swa
          dbus_dat_o    <= s2o_sdat;      // dmem req -> write for l.swa
        end
        else if (s2o_dc_refill_req) begin
          dbus_bsel_o   <= 4'b1111;         // dmem-req -> to-re-fill
          dbus_adr_o    <= s2o_phys_addr;   // dmem-req -> to-re-fill
        end
        else if (s2o_dbus_read_req) begin // dmem-req
          dbus_bsel_o   <= s2o_bsel;        // dmem-req -> dbus-read
          dbus_adr_o    <= s2o_phys_addr;   // dmem-req -> dbus-read
        end
      end // dmem-req

      DBUS_SBUF_READ: begin
        // DBUS controls
        dbus_bsel_o   <= sbuf_bsel;       // dbus-sbuf-read -> write
        dbus_adr_o    <= sbuf_phys_addr;  // dbus-sbuf-read -> write
        dbus_dat_o    <= sbuf_dat;        // dbus-sbuf-read -> write
        // Update data for potential DBUS error on write
        //  -- they make sense only if sbuf-err is raised
        sbuf_eear_o   <= sbuf_virt_addr;  // dbus-sbuf-read -> write : from buffer output
        sbuf_epcr_o   <= sbuf_epcr;       // dbus-sbuf-read -> write : from buffer output
      end // dbus-sbuf-read

      default:;
    endcase
  end // @ clock: DBUS_FSM


  // flush extender from pipeline-flush
  //  till DBUS transaction completion
  wire deassert_flush_r =
    dc_refill_allowed ? 1'b0 : // de-assert flush extender
    dc_refill_state   ? (dbus_err_i | (dbus_ack_i & dbus_burst_last_i)) : // de-assert flush extender
    dbus_read_state   ? (dbus_err_i | dbus_ack_i) : 1'b1; // de-assert flush extender
  // ---
  always @(posedge cpu_clk) begin
    if (cpu_rst)
      flush_r <= 1'b0; // on reset
    else if (deassert_flush_r)
      flush_r <= 1'b0; // on de-assert
    else if (pipeline_flush_i)
      flush_r <= 1'b1;
  end // @clock


  //-----------------------//
  // Store buffer instance //
  //-----------------------//

  // store buffer write controls
  assign sbuf_write = s2o_stna_req & (~sbuf_full) &         // STORE-BUFFER WRITE
                      (~s2o_snoop_proc) &                   // STORE-BUFFER WRITE
                      (~wrbk_lsu_miss_r) & grant_wrbk_to_lsu_i; // STORE-BUFFER WRITE
  // include exceptions and pipe flushing
  assign sbuf_we    = sbuf_write & (~s2o_excepts_addr) & (~pipeline_flush_i);

  // combined empty flag
  wire   sbuf_ram_empty;
  wire   sbuf_oreg_rdy;
  assign sbuf_empty = sbuf_ram_empty & (~sbuf_oreg_rdy);

  localparam STORE_BUFFER_NUM_TAPS = (1 << OPTION_STORE_BUFFER_DEPTH_WIDTH);

  // To store buffer (pc + virtual_address + physical_address + data + byte-sel)
  localparam STORE_BUFFER_DATA_WIDTH = (OPTION_OPERAND_WIDTH * 4) + (OPTION_OPERAND_WIDTH / 8);

  wire [STORE_BUFFER_DATA_WIDTH-1:0] sbuf_in;
  wire [STORE_BUFFER_DATA_WIDTH-1:0] sbuf_out;

  assign sbuf_in = {s2o_bsel, s2o_sdat, s2o_phys_addr, s2o_virt_addr, s2o_epcr};

  assign {sbuf_bsel, sbuf_dat, sbuf_phys_addr, sbuf_virt_addr, sbuf_epcr} = sbuf_out;

  // store buffer instance
  mor1kx_oreg_buff_marocchino
  #(
    .NUM_TAPS         (STORE_BUFFER_NUM_TAPS), // STORE_BUFFER
    .DATA_WIDTH       (STORE_BUFFER_DATA_WIDTH), // STORE_BUFFER
    .RAM_EMPTY_FLAG   ("ENABLED"), // STORE_BUFFER
    .REG_RDY_FLAG     ("ENABLED") // STORE_BUFFER
  )
  u_store_buffer
  (
    // clocks
    .cpu_clk      (cpu_clk), // STORE_BUFFER
    // resets
    .ini_rst      (cpu_rst), // STORE_BUFFER
    .ext_rst      (sbuf_err), // STORE_BUFFER
    // RW-controls
    .write_i      (sbuf_we), // STORE_BUFFER
    .read_i       (sbuf_read_state), // STORE_BUFFER
    // data input
    .data_i       (sbuf_in), // STORE_BUFFER
    // "RAM is empty" flag
    .ram_empty_o  (sbuf_ram_empty), // STORE_BUFFER
    // "RAM is full" flag
    .ram_full_o   (sbuf_full), // STORE_BUFFER
    // output register
    .rdy_o        (sbuf_oreg_rdy), // STORE_BUFFER
    .data_o       (sbuf_out) // STORE_BUFFER
  );


  //-------------------------//
  // Atomic operations logic //
  //-------------------------//

  assign dbus_swa_ack = dbus_swa_cmd_o & dbus_ack_i;
  // ---
  reg s2o_atomic_flag_set;
  reg s2o_atomic_flag_clear;
  // ---
  always @(posedge cpu_clk) begin
    if (flush_by_ctrl) begin  // reset/flush s2o- atomic set/clear flags
      s2o_atomic_flag_set   <= 1'b0;
      s2o_atomic_flag_clear <= 1'b0;
    end
    else if (dbus_swa_ack) begin        // determine  s2o- atomic set/clear flags
      s2o_atomic_flag_set   <=   dbus_atomic_flg_i;
      s2o_atomic_flag_clear <= (~dbus_atomic_flg_i);
    end
    else if (lsu_s3_adv) begin          // drop  s2o- atomic set/clear flags
      s2o_atomic_flag_set   <= 1'b0;
      s2o_atomic_flag_clear <= 1'b0;
    end
  end // @clock



  //-------------------------//
  // S2O_* control registers //
  //-------------------------//

  //
  // latch various load/store attributes
  //
  always @(posedge cpu_clk) begin
    if (lsu_s2_adv) begin
      // store command attributes
      s2o_epcr      <= s1o_sbuf_epcr;
      s2o_bsel      <= s2t_bsel;
      s2o_sdat      <= s2t_sdat;
      // load command attributes
      s2o_length    <= s1o_lsu_length;
      s2o_zext      <= s1o_lsu_zext;
      // virtual and physical addersses
      s2o_virt_addr <= s1o_virt_addr;
      s2o_phys_addr <= s2t_phys_addr;
    end
  end // @clock

  // latches for none atomic store command
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i) // reset any store command in stage #2
      s2o_op_lsu_store <= 1'b0;             // reset / flush
    else if (lsu_s2_adv)            // latch any store command in stage #2
      s2o_op_lsu_store <= s1o_op_lsu_store; // stage #2 advance
    else if (s3t_store_ack)         // clear any store command in stage #2
      s2o_op_lsu_store <= 1'b0;             // done
  end // @clock

  // none-atomic store command
  //  !!! keep dc_snoop2write in consistency with this !!!
  wire deassert_s2o_stna_req = sbuf_write | pipeline_flush_i | s2o_excepts_addr;
  // ---
  always @(posedge cpu_clk) begin
    if (cpu_rst) // drop l.swa command
      s2o_stna_req <= 1'b0; // by cpu reset
    else if (deassert_s2o_stna_req)
      s2o_stna_req <= 1'b0; // by deassert
    else if (lsu_s2_adv)    // latch none-atomic store command in stage #2
      s2o_stna_req <= s1o_op_lsu_store & (~s1o_op_lsu_atomic);
  end // @clock

  // atomic store command
  wire deassert_s2o_swa_req = dbus_swa_cmd_o ? (dbus_err_i | dbus_ack_i) : // deassert l.swa
                                               (pipeline_flush_i | s2o_excepts_addr); // deassert l.swa
  //---
  always @(posedge cpu_clk) begin
    if (cpu_rst) // drop l.swa command
      s2o_swa_req <= 1'b0; // by cpu reset
    else if (deassert_s2o_swa_req)
      s2o_swa_req <= 1'b0; // by deassert
    else if (lsu_s2_adv) // latch l.swa store command in stage #2
      s2o_swa_req <= s1o_op_lsu_store & s1o_op_lsu_atomic;
  end // @clock


  // --- DCACHE re-fill request ---
  wire deassert_s2o_dc_refill_req =
    dc_refill_allowed ? 1'b0 : // de-assert re-fill request
      (dc_refill_state ? (dbus_err_i | (dbus_ack_i & dbus_burst_last_i)) : // de-assert re-fill request
                         (pipeline_flush_i | s2o_excepts_addr)); // de-assert re-fill request
  // ---
  always @(posedge cpu_clk) begin
    if (cpu_rst)
      s2o_dc_refill_req <= 1'b0;              // reset / flush
    else if (deassert_s2o_dc_refill_req)
      s2o_dc_refill_req <= 1'b0;              // re-fill done or canceled
    else if (lsu_s2_adv)
      s2o_dc_refill_req <= s2t_dc_refill_req;
  end // @ clock
  // --- DCACHE ack ---
  always @(posedge cpu_clk) begin
    if (flush_by_ctrl)
      s2o_dc_ack_read <= 1'b0;  // reset / flush
    else if (lsu_s2_adv)        // rise dc-ack-read
      s2o_dc_ack_read <= s2t_dc_ack_read;
    else if (lsu_s3_adv)        // drop dc-ack-read
      s2o_dc_ack_read <= 1'b0;  // WriteBack/Pending is taking result
  end // @ clock
  // --- DCACHE data ---
  always @(posedge cpu_clk) begin
    if (lsu_s2_adv)             // latch DCACHE data
      s2o_dc_dat <= s2t_dc_dat;
  end // @ clock


  // --- DBUS read request ---
  wire deassert_s2o_dbus_read_req =
    dbus_read_state ? (dbus_err_i | dbus_ack_i) :             // de-assert dbus read request
                      (pipeline_flush_i | s2o_excepts_addr);  // de-assert dbus read request
  // ---
  always @(posedge cpu_clk) begin
    if (cpu_rst) begin
      s2o_dbus_read_req <= 1'b0;          // cpu-reset
      s2o_lwa_req       <= 1'b0;          // cpu-reset
    end
    else if (deassert_s2o_dbus_read_req) begin
      s2o_dbus_read_req <= 1'b0;          // dbus read done or canceled
      s2o_lwa_req       <= 1'b0;          // dbus read done or canceled
    end
    else if (lsu_s2_adv) begin
      s2o_dbus_read_req <= s2t_dbus_read_req;
      s2o_lwa_req       <= s1o_op_lsu_load & s1o_op_lsu_atomic;
    end
  end // @ clock
  // --- combined DBUS-load/SBUFF-store ACK ---
  always @(posedge cpu_clk) begin
    if (flush_by_ctrl)
      s3o_ls_ack <= 1'b0;                     // reset / flush
    else if (dbus_load_ack | s3t_store_ack)   // rise combined DBUS-load/ANY-store s3o-ACK
      s3o_ls_ack <= 1'b1;                     // dbus-load-ack OR s3t-store-ack
    else if (lsu_s3_adv)                      // drop combined DBUS-load/ANY-store s3o-ACK
      s3o_ls_ack <= 1'b0;                     // WriteBack/Pending is taking result
  end // @ clock
  // --- DBUS load data ---
  always @(posedge cpu_clk) begin
    if (dbus_load_ack)            // latch DBUS read data
      s2o_dbus_dat <= dbus_dat_i;
  end // @ clock


  // --- latches for exceptions ---
  always @(posedge cpu_clk) begin
    if (flush_by_ctrl) begin
      // address conversion exceptions
      s2o_tlb_miss       <= 1'b0; // reset / flush
      s2o_pagefault      <= 1'b0; // reset / flush
      s2o_align          <= 1'b0; // reset / flush
      // "instant" (not related to STORE_BUFFER) DBUS error
      s2o_dbus_err_nsbuf <= 1'b0; // reset / flush
      // combined exceptions
      s2o_excepts_addr   <= 1'b0; // reset / flush
      s2o_excepts_any    <= 1'b0; // reset / flush
    end
    else if (lsu_s2_adv) begin                  // latch address conversion exceptions
      // address conversion exceptions
      s2o_tlb_miss       <= s2t_tlb_miss;
      s2o_pagefault      <= s2t_pagefault;
      s2o_align          <= s2t_align;
      // combined exceptions
      s2o_excepts_addr   <= s2t_excepts_addr;
      s2o_excepts_any    <= s2t_excepts_addr;
    end
    else if (dbus_err_i) begin                  // rise s2o_* DBUS error
      s2o_dbus_err_nsbuf <= s3t_dbus_err_nsbuf; // at a DBUS error
      s2o_excepts_any    <= 1'b1;               // at a DBUS error
    end
  end // @clock


  // --- "operation complete" and "LSU valid" ---
  assign lsu_s2_rdy  = s2o_dc_ack_read | s3o_ls_ack | s2o_excepts_any;
  // --- "operation complete" and "LSU valid" ---
  assign lsu_valid_o = lsu_s2_rdy | wrbk_lsu_miss_r;
  //--- "WriteBack miss" flag ---
  always @(posedge cpu_clk) begin
    if (flush_by_ctrl)
      wrbk_lsu_miss_r <= 1'b0;
    else if (padv_wrbk_i & grant_wrbk_to_lsu_i)
      wrbk_lsu_miss_r <= 1'b0;
    else if (lsu_s3_adv)    // rise wrbk-lsu-miss
      wrbk_lsu_miss_r <= 1'b1;
  end // @clock


  //-----------------//
  // LSU load output //
  //-----------------//

  wire [LSUOOW-1:0] s3t_ldat = s2o_dc_ack_read ? s2o_dc_dat : s2o_dbus_dat;

  // Select part of bus for load
  reg [LSUOOW-1:0] s3t_ldat_aligned;
  // ---
  always @(s2o_virt_addr[1:0] or s3t_ldat) begin
    // synthesis parallel_case
    case(s2o_virt_addr[1:0])
      2'b00: s3t_ldat_aligned = s3t_ldat;
      2'b01: s3t_ldat_aligned = {s3t_ldat[23:0],8'd0};
      2'b10: s3t_ldat_aligned = {s3t_ldat[15:0],16'd0};
      2'b11: s3t_ldat_aligned = {s3t_ldat[7:0],24'd0};
    endcase
  end

  // Do appropriate extension for load
  reg [LSUOOW-1:0] s3t_ldat_extended;
  // ---
  always @(s2o_zext or s2o_length or s3t_ldat_aligned) begin
    // synthesis parallel_case
    case({s2o_zext, s2o_length})
      3'b100:  s3t_ldat_extended = {24'd0,s3t_ldat_aligned[31:24]}; // lbz
      3'b101:  s3t_ldat_extended = {16'd0,s3t_ldat_aligned[31:16]}; // lhz
      3'b000:  s3t_ldat_extended = {{24{s3t_ldat_aligned[31]}},
                                    s3t_ldat_aligned[31:24]}; // lbs
      3'b001:  s3t_ldat_extended = {{16{s3t_ldat_aligned[31]}},
                                    s3t_ldat_aligned[31:16]}; // lhs
      default: s3t_ldat_extended = s3t_ldat_aligned;
    endcase
  end


  // LSU's output data set registered by WriteBack miss
  // Write-Back-output assignement
  reg  [LSUOOW-1:0] s3o_lsu_result;
  reg  [LSUOOW-1:0] s3o_lsu_except_addr;
  // Atomic operation flag set/clear logic
  reg               s3o_atomic_flag_set;
  reg               s3o_atomic_flag_clear;
  // Particular LSU exception flags
  reg               s3o_dbus_err_nsbuf;
  reg               s3o_pagefault;
  reg               s3o_tlb_miss;
  reg               s3o_align;
  // Any exception
  reg               s3o_excepts_any;
  
  // ---
  always @(posedge cpu_clk) begin
    if (lsu_s3_adv) begin // save output data set in "miss" register
      // Write-Back-output assignement
      s3o_lsu_result        <= s3t_ldat_extended;
      s3o_lsu_except_addr   <= s2o_virt_addr;
      // Atomic operation flag set/clear logic
      s3o_atomic_flag_set   <= s2o_atomic_flag_set;
      s3o_atomic_flag_clear <= s2o_atomic_flag_clear;
      // Particular LSU exception flags
      s3o_dbus_err_nsbuf    <= s2o_dbus_err_nsbuf;
      s3o_pagefault         <= s2o_pagefault;
      s3o_tlb_miss          <= s2o_tlb_miss;
      s3o_align             <= s2o_align;
      // Any exception
      s3o_excepts_any       <= s2o_excepts_any;
    end
  end // @clock

  // pre-Write-Back exceprions & errors
  assign exec_an_except_lsu_o = (wrbk_lsu_miss_r ? s3o_excepts_any : s2o_excepts_any) & grant_wrbk_to_lsu_i;

  // Write-Back-registered load result and exception address
  always @(posedge cpu_clk) begin
    if (padv_wrbk_i) begin
      if (grant_wrbk_to_lsu_i) begin
        wrbk_lsu_result_o      <= wrbk_lsu_miss_r ? s3o_lsu_result : s3t_ldat_extended;
        wrbk_lsu_except_addr_o <= wrbk_lsu_miss_r ? s3o_lsu_except_addr : s2o_virt_addr;
      end
      else begin
        wrbk_lsu_result_o      <= {LSUOOW{1'b0}};
      end
    end
  end // @clock

  // Write-Back-registered atomic flag and exception flags
  always @(posedge cpu_clk) begin
    if (padv_wrbk_i & grant_wrbk_to_lsu_i) begin
      // Atomic operation flag set/clear logic
      wrbk_atomic_flag_set_o   <= wrbk_lsu_miss_r ? s3o_atomic_flag_set   : s2o_atomic_flag_set;
      wrbk_atomic_flag_clear_o <= wrbk_lsu_miss_r ? s3o_atomic_flag_clear : s2o_atomic_flag_clear;
      // Particular LSU exception flags
      wrbk_except_dbus_err_o   <= wrbk_lsu_miss_r ? s3o_dbus_err_nsbuf : s2o_dbus_err_nsbuf;
      wrbk_except_dpagefault_o <= wrbk_lsu_miss_r ? s3o_pagefault      : s2o_pagefault;
      wrbk_except_dtlb_miss_o  <= wrbk_lsu_miss_r ? s3o_tlb_miss       : s2o_tlb_miss;
      wrbk_except_dbus_align_o <= wrbk_lsu_miss_r ? s3o_align          : s2o_align;
    end
    else begin
      // Atomic operation flag set/clear logic
      wrbk_atomic_flag_set_o   <= 1'b0; // 1-clk-length
      wrbk_atomic_flag_clear_o <= 1'b0; // 1-clk-length
      // Particular LSU exception flags
      wrbk_except_dbus_err_o   <= 1'b0; // 1-clk-length
      wrbk_except_dpagefault_o <= 1'b0; // 1-clk-length
      wrbk_except_dtlb_miss_o  <= 1'b0; // 1-clk-length
      wrbk_except_dbus_align_o <= 1'b0; // 1-clk-length
    end
  end // @clock
  
endmodule // mor1kx_lsu_marocchino
