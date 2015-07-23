/* ****************************************************************************
  This Source Code Form is subject to the terms of the
  Open Hardware Description License, v. 1.0. If a copy
  of the OHDL was not distributed with this file, You
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: mor1kx fetch/address stage unit for MAROCCHINO pipeline

  basically an interface to the ibus/icache subsystem that can react to
  exception and branch signals.

  refactored version of mor1kx_fetch_cappuccino

  Copyright (C) 2012 Authors

  Author(s): Julius Baxter <juliusbaxter@gmail.com>
             Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>

  Copyright (C) 2015 Authors

  Author(s): Andrey Bacherov <avbacherov@opencores.org>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_fetch_marocchino
#(
  parameter OPTION_OPERAND_WIDTH       = 32,
  parameter OPTION_RESET_PC            = {{(OPTION_OPERAND_WIDTH-13){1'b0}},
                                          `OR1K_RESET_VECTOR,8'd0},
  parameter OPTION_RF_ADDR_WIDTH       =  5,
  // cache configuration
  parameter OPTION_ICACHE_BLOCK_WIDTH  =  5,
  parameter OPTION_ICACHE_SET_WIDTH    =  9,
  parameter OPTION_ICACHE_WAYS         =  2,
  parameter OPTION_ICACHE_LIMIT_WIDTH  = 32,
  // mmu configuration
  parameter FEATURE_IMMU_HW_TLB_RELOAD = "NONE",
  parameter OPTION_IMMU_SET_WIDTH      = 6,
  parameter OPTION_IMMU_WAYS           = 1
)
(
  // clock and reset
  input                                 clk,
  input                                 rst,

  // pipeline control
  input                                 padv_fetch_i,
  input                                 padv_decode_i,
  input                                 dcod_bubble_i,
  input                                 pipeline_flush_i,

  // configuration
  input                                 ic_enable_i,
  input                                 immu_enable_i,
  input                                 supervisor_mode_i,

  // SPR interface
  //  input
  input [15:0]                          spr_bus_addr_i,
  input                                 spr_bus_we_i,
  input                                 spr_bus_stb_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_i,
  //  output from cache
  output     [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_ic_o,
  output                                spr_bus_ack_ic_o,
  //  output from immu
  output     [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_immu_o,
  output                                spr_bus_ack_immu_o,

  // interface to ibus
  input                                 ibus_err_i,
  input                                 ibus_ack_i,
  input          [`OR1K_INSN_WIDTH-1:0] ibus_dat_i,
  output                                ibus_req_o,
  output     [OPTION_OPERAND_WIDTH-1:0] ibus_adr_o,
  output                                ibus_burst_o,

  // branch/jump control transfer
  input                                 dcod_take_branch_i,
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_branch_target_i,
  input                                 branch_mispredict_i,
  input      [OPTION_OPERAND_WIDTH-1:0] exec_mispredict_target_i,
  // exception/rfe control transfer
  input                                 ctrl_branch_exception_i,
  input      [OPTION_OPERAND_WIDTH-1:0] ctrl_branch_except_pc_i,
  // debug unit command for control transfer
  input                                 du_restart_i,
  input      [OPTION_OPERAND_WIDTH-1:0] du_restart_pc_i,

  // to RF
  output     [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfa_adr_o,
  output     [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfb_adr_o,
  output                                fetch_rf_adr_valid_o,
  // to CTRL
  output                                fetch_valid_o,
  // to DECODE
  output reg [OPTION_OPERAND_WIDTH-1:0] pc_decode_o,
  output reg     [`OR1K_INSN_WIDTH-1:0] dcod_insn_o,
  output reg                            dcod_insn_valid_o,
  // exceptions
  output reg                            dcod_except_ibus_err_o,
  output reg                            dcod_except_itlb_miss_o,
  output reg                            dcod_except_ipagefault_o,
  output reg                            fetch_exception_taken_o
);

  /*
     Definitions:
       s??o_name - "S"tage number "??", "O"utput
       s??t_name - "S"tage number "??", "T"emporary (internally)
  */

  /* MMU related controls and signals */

  // Flag to take into accaunt address translation.
  reg                             immu_enabled_r;
  // Supervisor mode for IMMU
  reg                             immu_svmode_r;
  // mmu's regular output
  wire [OPTION_OPERAND_WIDTH-1:0] immu_phys_addr;
  wire                            immu_cache_inhibit;
  // mmu exceptions (valid for enabled mmu only)
  wire                            except_itlb_miss;
  wire                            except_ipagefault;
  wire                            immu_an_except; 
  /* HW reload TLB related (MAROCCHINO_TODO : not implemented yet)
  wire                            tlb_reload_req;
  reg                             tlb_reload_ack;
  wire [OPTION_OPERAND_WIDTH-1:0] tlb_reload_addr;
  reg  [OPTION_OPERAND_WIDTH-1:0] tlb_reload_data;
  wire                            tlb_reload_pagefault;
  wire                            tlb_reload_busy; */


  /* ICACHE related controls and signals */

  // Access ICACHE indication
  wire                        ic_enabled;
  wire                        ic_access;
  //   Hack? Work around MMU?
  // Today the thing is actual for DCACHE only.
  // Addresses 0x8??????? are treated as non-cacheble regardless MMU's flag.
  wire                        ic_check_limit_width;
  // ICACHE output ready (by read or re-fill)
  wire                        ic_rdy;
  // ICACHE module <-> IBUS state machine
  wire                        ic_refill;
  wire                        ic_refill_req;
  wire                        ic_refill_done;
  // ICACHE module <-> FETCH pipe
  wire                        ic_req;
  wire                        ic_ack;
  wire [`OR1K_INSN_WIDTH-1:0] ic_dat;


  /* IBUS access state machine controls */

  //   IBUS output ready
  // Indicates IBUS ACK for IBUS direct access only
  // (not ACKs for ICACHE refill):
  wire                            ibus_rdy;
  // IBUS FSM statuses
  wire                            ibus_fsm_busy;
  wire                            ibus_fsm_stop;
  // IBUS access state machine
  localparam                [2:0] IDLE       = 0,
                                  READ       = 1,
                                  TLB_RELOAD = 2,
                                  IC_REFILL  = 3;
  //
  reg                       [2:0] state;
  // request IBUS transaction
  reg                             ibus_req_r;
  // address for IBUS transaction
  reg  [OPTION_OPERAND_WIDTH-1:0] ibus_adr_r;
  wire [OPTION_OPERAND_WIDTH-1:0] next_ibus_adr;
  // IBUS error processing
  wire                            except_ibus_err;  // instant|stored


  /* ICACHE/IBUS requests and nswers */

  // The logic is located in Stage #2 section

  // Request & Ready
  reg                         imem_req_r; // next insn request
  wire                        imem_rdy;   // next insn ready flad
  //   ACK/DATA stored
  // They passed (if ready) to stage #2 output latches @ next advance
  reg                         imem_ic_ack_stored;
  reg  [`OR1K_INSN_WIDTH-1:0] imem_ic_dat_stored;
  reg                         imem_ibus_ack_stored;
  reg  [`OR1K_INSN_WIDTH-1:0] imem_ibus_dat_stored;

  /* Wires & registers are used across FETCH pipe stages */

  // Flush processing
  wire flush_by_ctrl;       // flush registers from pipeline-flush command till IBUS transaction completion
  wire flush_by_branch;     // flush some registers if branch processing
  wire flush_by_mispredict; // flush some registers if mispredict branch processing

  // Support access through SPR BUS
  //   For MAROCCHINO SPR access means that pipeline is stalled till ACK.
  // So, no padv-*, but we delay SPR access command till IBUS transaction
  // completion.
  reg  spr_bus_ic_cs_r;    // STB-signal to ICACHE after IBUS transaction completion
  reg  spr_bus_immu_cs_r;  // STB-signal to IMMU   after IBUS transaction completion
  wire assert_spr_bus_req; // flag to rise spr-bus-ic(immu)-cs-r

  // Stage #1 is stalled due to ICACHE refill, IBUS access or Exceptions
  wire stall_s1;
  reg  stall_r;
  wire deassert_stall;

  // ICACHE/IMMU match address store register
  //   The register operates in the same way
  // as memory blocks in ICACHE/IMMU to provide correct
  // address for comparision on output of ICACHE/MMU memory blocks.
  //   It is also play role of virtual address store to use
  // in cases of ICACHE miss, stalling due to exceptions
  // or till IBUS answer and restart fetching after SPR transaction.
  reg [OPTION_OPERAND_WIDTH-1:0] s1o_virt_addr;

  // valid instruction on stage #2 outputs
  wire s3t_insn;


  // Advance stage #1
  wire padv_s1 = padv_fetch_i & ~stall_s1 & ~flush_by_ctrl;
  // Advance output latches
  wire padv_s3 = padv_decode_i & ~dcod_bubble_i;

  // combined MMU's and IBUS's exceptions
  wire fetch_excepts = immu_an_except | except_ibus_err;


  /***********************/
  /* Stage #1: PC update */
  /***********************/


  // jumb/branch in decode and delay slot is fetched (at Stage #2 output)
  wire take_branch = dcod_take_branch_i & s3t_insn;
  // store branch flag and target if stage #1 is stalled
  reg                            branch_stored;
  reg [OPTION_OPERAND_WIDTH-1:0] branch_target_stored;
  //
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      branch_stored        <= 1'b0;
      branch_target_stored <= OPTION_RESET_PC;
    end
    //   (a) don't store but take branch directly from DECODE
    //   (b) don't store if DECODE bubble (padv-s1 is 0 for the case)
    // (i.e. dcod-branch-target-i isn't computed)
    //   (c) don't store / clear if pipeline flush
    else if (padv_s1 | dcod_bubble_i | flush_by_ctrl) begin
      branch_stored        <= 1'b0;
      branch_target_stored <= branch_target_stored;
    end
    // store branch if IBUS-machine is busy
    else if (take_branch & ~branch_stored) begin
      branch_stored        <= 1'b1;
      branch_target_stored <= dcod_branch_target_i;
    end
  end // @ clock
  // flush some registers if branch processing
  assign flush_by_branch = take_branch | branch_stored;


  // flag that mispredict has been taken
  reg mispredict_taken_r;
  // ----
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      mispredict_taken_r <= 1'b0;
    // mispedict moves out from EXECUTE
    else if (padv_decode_i | flush_by_ctrl)
      mispredict_taken_r <= 1'b0;
    // take mispredict
    else if (padv_s1 & branch_mispredict_i & ~mispredict_taken_r)
      mispredict_taken_r <= 1'b1;
  end // @ clock
  // store mispredict flag and target if stage #1 is stalled
  // (similar to branch case)
  reg                            mispredict_stored;
  reg [OPTION_OPERAND_WIDTH-1:0] mispredict_target_stored;
  // ----
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      mispredict_stored        <= 1'b0;
      mispredict_target_stored <= OPTION_RESET_PC;
    end
    // (a) don't store but take mispredict directly from EXECUTE
    // (b) don't store if mispredict has been already taken
    // (c) don't store / clear if pipeline flush
    else if (padv_s1 | mispredict_taken_r | flush_by_ctrl) begin
      mispredict_stored        <= 1'b0;
      mispredict_target_stored <= mispredict_target_stored;
    end
    // store mispredict if IBUS-machine is busy
    else if (branch_mispredict_i & ~mispredict_stored) begin
      mispredict_stored        <= 1'b1;
      mispredict_target_stored <= exec_mispredict_target_i;
    end
  end // @ clock
  // flush some registers if mispredict branch processing
  assign flush_by_mispredict = (branch_mispredict_i & ~mispredict_taken_r) | mispredict_stored;


  // Select the PC for next fetching
  wire [OPTION_OPERAND_WIDTH-1:0] s1t_pc_mux =
    // Debug (MAROCCHINO_TODO)
    du_restart_i                                 ? du_restart_pc_i :
    // on stall or during SPR access (because no padv-*)
    ~padv_s1                                     ? s1o_virt_addr :
    // padv-s1
    (ctrl_branch_exception_i                     ? ctrl_branch_except_pc_i :
     (branch_mispredict_i & ~mispredict_taken_r) ? exec_mispredict_target_i :
     mispredict_stored                           ? mispredict_target_stored :
     take_branch                                 ? dcod_branch_target_i :
     branch_stored                               ? branch_target_stored :
                                                   (s1o_virt_addr + 4));

  // 1-clock fetch-exception-taken
  // The flush-by-ctrl is dropped synchronously with s1-stall
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      fetch_exception_taken_o <= 1'b0;
    else if (padv_s1)
      fetch_exception_taken_o <= ctrl_branch_exception_i;
    else
      fetch_exception_taken_o <= 1'b0;
  end // @ clock


  /*****************************************/
  /* Stage #2: IMMU / ICACHE / IBUS access */
  /*****************************************/


  // Force switching ICACHE/IMMU off in case of IMMU-generated exceptions
  wire immu_rst_excepts = (immu_an_except & flush_by_ctrl);

  // Update IMMU enable/disable and Supervisor mode.
  //   For masking MMU flags (exceptions & cache-inhibit) and
  // select source of physical address for check cache hit.
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      immu_enabled_r <= 1'b0;
      immu_svmode_r  <= 1'b0;
    end
    else if (immu_rst_excepts) begin // IMMU -> off
      immu_enabled_r <= 1'b0;
      immu_svmode_r  <= immu_svmode_r;
    end
    else if (padv_s1) begin
      immu_enabled_r <= immu_enable_i;
      immu_svmode_r  <= supervisor_mode_i;
    end
  end // @ clock

  // Update ICACHE enable/disable.
  reg ic_enabled_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      ic_enabled_r <= 1'b0;
    else if (immu_rst_excepts | assert_spr_bus_req) // ICAHCE -> idle
      ic_enabled_r <= 1'b0;
    else if (padv_s1)
      ic_enabled_r <= ic_enable_i;
  end // @ clock
  //   Force ICACHE go to idle state if either SPR access is requested
  // or IMMU-generated exceptions is cleaned
  assign ic_enabled = ~immu_rst_excepts & ~assert_spr_bus_req & ic_enabled_r;

  // ICACHE/IMMU match address store register
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      s1o_virt_addr <= OPTION_RESET_PC - 4; // will be restored on 1st advance
    else if (padv_s1)
      s1o_virt_addr <= s1t_pc_mux;
  end // @ clock

  // Select physical address depending on IMMU enabled/disabled
  wire [OPTION_OPERAND_WIDTH-1:0] s2t_phys_addr_mux =
    immu_enabled_r ? immu_phys_addr : s1o_virt_addr;

  //----------------------------------------//
  // IBUS/ICACHE <-> FETCH's pipe interface //
  //----------------------------------------//

  assign imem_rdy = ic_rdy | ibus_rdy;

  // Flag indicating that ICACHE/MMU have taken new address
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      imem_req_r <= 1'b0;
    else if (padv_s1)
      imem_req_r <= 1'b1;
    else if (imem_rdy | fetch_excepts)
      imem_req_r <= 1'b0;
  end // @ clock

  // ACKs and DATA stored till nearest advance
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      // ACKs
      imem_ic_ack_stored   <= 1'b0;
      imem_ibus_ack_stored <= 1'b0;
      // DATA
      imem_ic_dat_stored   <= {`OR1K_OPCODE_NOP,26'd0};
      imem_ibus_dat_stored <= {`OR1K_OPCODE_NOP,26'd0};
    end
    else if (padv_fetch_i | fetch_excepts | flush_by_ctrl) begin
      // ACKs
      imem_ic_ack_stored   <= 1'b0;
      imem_ibus_ack_stored <= 1'b0;
      // DATA
      imem_ic_dat_stored   <= {`OR1K_OPCODE_NOP,26'd0};
      imem_ibus_dat_stored <= {`OR1K_OPCODE_NOP,26'd0};
    end
    else if (imem_rdy) begin
      // ACKs
      imem_ic_ack_stored   <= ic_rdy;
      imem_ibus_ack_stored <= ibus_rdy;
      // DATA
      imem_ic_dat_stored   <= ic_dat;
      imem_ibus_dat_stored <= ibus_dat_i;
    end
  end // @ clock

  //-------------------------//
  // Stage #2 output latches //
  //-------------------------//

  // block ACKs by various reasons (stall includes exceptions)
  wire s2t_ack_enable = ~flush_by_branch & ~flush_by_mispredict & ~fetch_excepts;

  // masked ACKs
  wire s2t_ic_ack_instant   = ic_rdy               & s2t_ack_enable;
  wire s2t_ibus_ack_instant = ibus_rdy             & s2t_ack_enable;
  wire s2t_ic_ack_stored    = imem_ic_ack_stored   & s2t_ack_enable;
  wire s2t_ibus_ack_stored  = imem_ibus_ack_stored & s2t_ack_enable;

  // to s3: instruction valid flags
  reg s2o_ic_ack_instant, s2o_ibus_ack_instant;
  reg s2o_ic_ack_stored,  s2o_ibus_ack_stored;
  //   To minimize number of multiplexors we
  // latche all instuction sources and their validity flags.
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      s2o_ic_ack_instant   <= 1'b0;
      s2o_ibus_ack_instant <= 1'b0;
      s2o_ic_ack_stored    <= 1'b0;
      s2o_ibus_ack_stored  <= 1'b0;
    end
    else if (flush_by_ctrl) begin
      s2o_ic_ack_instant   <= 1'b0;
      s2o_ibus_ack_instant <= 1'b0;
      s2o_ic_ack_stored    <= 1'b0;
      s2o_ibus_ack_stored  <= 1'b0;
    end
    else if (padv_fetch_i) begin
      s2o_ic_ack_instant   <= s2t_ic_ack_instant;
      s2o_ibus_ack_instant <= s2t_ibus_ack_instant;
      s2o_ic_ack_stored    <= s2t_ic_ack_stored;
      s2o_ibus_ack_stored  <= s2t_ibus_ack_stored;
    end
  end // @ clock

  // to s3: instruction words
  reg [`OR1K_INSN_WIDTH-1:0] s2o_ic_dat_instant;
  reg [`OR1K_INSN_WIDTH-1:0] s2o_ibus_dat_instant;
  reg [`OR1K_INSN_WIDTH-1:0] s2o_ic_dat_stored;
  reg [`OR1K_INSN_WIDTH-1:0] s2o_ibus_dat_stored;
  //   To minimize number of multiplexors we
  // latche all instuction sources and their validity flags.
  always @(posedge clk `OR_ASYNC_RST) begin
    if (padv_fetch_i) begin
      s2o_ic_dat_instant   <= ic_dat;
      s2o_ibus_dat_instant <= ibus_dat_i;
      s2o_ic_dat_stored    <= imem_ic_dat_stored;
      s2o_ibus_dat_stored  <= imem_ibus_dat_stored;
    end
  end // @ clock

  // to s3: exception flags
  reg s2o_ibus_err;
  reg s2o_itlb_miss;
  reg s2o_ipagefault;
  // Exceptions: go to pipe around stall logic
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      s2o_ibus_err   <= 1'b0;
      s2o_itlb_miss  <= 1'b0;
      s2o_ipagefault <= 1'b0;
    end
    else if (flush_by_ctrl) begin
      s2o_ibus_err   <= 1'b0;
      s2o_itlb_miss  <= 1'b0;
      s2o_ipagefault <= 1'b0;
    end
    else if (padv_fetch_i) begin
      s2o_ibus_err   <= except_ibus_err;
      s2o_itlb_miss  <= except_itlb_miss;
      s2o_ipagefault <= except_ipagefault;
    end
  end // @ clock

  // to s3: program counter
  reg [OPTION_OPERAND_WIDTH-1:0] s2o_pc;
  // ----
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      s2o_pc <= OPTION_RESET_PC;
    else if (padv_fetch_i)
      s2o_pc <= s1o_virt_addr;
  end // @ clock

  // to CTRL: valid flag (new insn is available)
  wire s2t_insn = s2t_ic_ack_instant | s2t_ibus_ack_instant |
                  s2t_ic_ack_stored  | s2t_ibus_ack_stored;
  // stage #2 valid flag
  reg s2o_valid;
  // ----
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      s2o_valid <= 1'b0;
    else if (flush_by_ctrl)
      s2o_valid <= 1'b0;
    else if (padv_fetch_i)
      s2o_valid <= s2t_insn | fetch_excepts;
  end // @ clock
  // output valid flag
  assign fetch_valid_o = s2o_valid;


  /*****************************************/
  /* Stage #3: delay slot & output latches */
  /*****************************************/


  // exceptions on stage #2 output
  wire s3t_itlb_miss  = s2o_itlb_miss  & ~flush_by_mispredict;
  wire s3t_ipagefault = s2o_ipagefault & ~flush_by_mispredict;

  wire s3t_excepts = s2o_ibus_err | s3t_itlb_miss | s3t_ipagefault;

  // valid instruction
  assign s3t_insn = (s2o_ic_ack_instant | s2o_ibus_ack_instant |
                     s2o_ic_ack_stored  | s2o_ibus_ack_stored) & ~flush_by_mispredict;

  // select insn
  wire [OPTION_OPERAND_WIDTH-1:0] s3t_insn_mux =
    ~s3t_insn            ? {`OR1K_OPCODE_NOP,26'd0} :
    s2o_ic_ack_instant   ? s2o_ic_dat_instant :
    s2o_ibus_ack_instant ? s2o_ibus_dat_instant :
    s2o_ic_ack_stored    ? s2o_ic_dat_stored :
                           s2o_ibus_dat_stored;

  // to DECODE: instruction word
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      dcod_insn_o <= {`OR1K_OPCODE_NOP,26'd0};
    else if (flush_by_ctrl)
      dcod_insn_o <= {`OR1K_OPCODE_NOP,26'd0};
    else if (padv_s3)
      dcod_insn_o <= s3t_insn_mux;
  end // @ clock

  // to DECODE: actual program counter
  // condition for advancing PC
  wire s3t_padv_pc = padv_s3 & ~flush_by_ctrl & (~flush_by_mispredict | s3t_excepts);
  // ----
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      pc_decode_o <= OPTION_RESET_PC;
    else if (s3t_padv_pc)
      pc_decode_o <= s2o_pc;
  end // @ clock

  // to DECODE: instruction valid flag
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      dcod_insn_valid_o <= 1'b0;
    else if (flush_by_ctrl)
      dcod_insn_valid_o <= 1'b0;
    else if (padv_s3)
      dcod_insn_valid_o <= s3t_insn | s3t_excepts;
  end // @ clock

  // exceptions
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      dcod_except_ibus_err_o   <= 1'b0;
      dcod_except_itlb_miss_o  <= 1'b0;
      dcod_except_ipagefault_o <= 1'b0;
    end
    else if (flush_by_ctrl) begin
      dcod_except_ibus_err_o   <= 1'b0;
      dcod_except_itlb_miss_o  <= 1'b0;
      dcod_except_ipagefault_o <= 1'b0;
    end
    else if (padv_s3) begin
      dcod_except_ibus_err_o   <= s2o_ibus_err;
      dcod_except_itlb_miss_o  <= s3t_itlb_miss;
      dcod_except_ipagefault_o <= s3t_ipagefault;
    end
  end // @ clock

  // to RF
  assign fetch_rfa_adr_o      = s3t_insn_mux[`OR1K_RA_SELECT];
  assign fetch_rfb_adr_o      = s3t_insn_mux[`OR1K_RB_SELECT];
  assign fetch_rf_adr_valid_o = padv_s3 & s3t_insn & ~flush_by_ctrl;


  /********** End of FETCH pipe. Start other logics. **********/

  //-----------------------//
  // Stall and flush logic //
  //-----------------------//

  // detect stall: new request but no answer yet or exceptions
  wire assert_stall = ~stall_r & (ibus_fsm_busy | fetch_excepts);

  // deassert stall state on next posedge clock
  //   MAROCCHINO_TODO. Potential improvement:
  // Additionally to ibus-fsm-busy use transitions
  // "a state" -> IDLE to speed up de-assert stall?
  assign deassert_stall = stall_r & ibus_fsm_stop & ~fetch_excepts;

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      stall_r <= 1'b0;
    else if (deassert_stall)
      stall_r <= 1'b0;
    else if (assert_stall)
      stall_r <= 1'b1;
  end // @ clock

  assign stall_s1 = assert_stall | stall_r;


  // store flush command till IBUS transactions complete
  reg flush_r;
  // ----
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      flush_r <= 1'b0;
    else if (deassert_stall)
      flush_r <= 1'b0;
    else if (stall_s1 & pipeline_flush_i)
      flush_r <= 1'b1;
  end // @ clock

  // combination of pipeline-flush and flush-r
  assign flush_by_ctrl = pipeline_flush_i | flush_r;

  //--------------------//
  // IBUS state machine //
  //--------------------//

  // IBUS error processing
  wire ibus_err_instant; // error reported "just now"
  reg  ibus_err_r;       // error stored for exception processing
  // IBUS error during IBUS access
  assign ibus_err_instant = ibus_req_r & ibus_err_i & ~flush_by_ctrl;
  // IBUS error stored for exception processing
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      ibus_err_r <= 1'b0;
    else if (flush_by_ctrl)
      ibus_err_r <= 1'b0;
    else if (ibus_err_instant)
      ibus_err_r <= 1'b1;
  end // @ clock
  // instant|stored IBUS error
  assign except_ibus_err = ibus_err_instant | ibus_err_r;

  // IBUS output ready (no bus error case)
  // !!! should follows appropriate FSM condition,
  assign ibus_rdy = (state == READ) & ibus_ack_i & ~fetch_excepts;

  // IBUS FSM status is busy
  // !!! should follows appropriate FSM condition,
  //     but without taking into account exceotions
  assign ibus_fsm_busy = (state != IDLE) | ((state == IDLE) & imem_req_r & ~ic_rdy);

  // IBUS FSM status is busy
  // !!! should follows appropriate FSM condition,
  //     but without taking into account exceotions
  assign ibus_fsm_stop = (state == IDLE) & ~imem_req_r;

  // refill support
  assign next_ibus_adr = (OPTION_ICACHE_BLOCK_WIDTH == 5) ?
    {ibus_adr_r[31:5], ibus_adr_r[4:0] + 5'd4} : // 32 byte
    {ibus_adr_r[31:4], ibus_adr_r[3:0] + 4'd4};  // 16 byte

  // state machine itself
  always @(posedge clk `OR_ASYNC_RST) begin
    // states
    case (state)
      IDLE: begin
        ibus_req_r <= 1'b0;
        if (imem_req_r & ~ic_rdy & ~fetch_excepts) begin
          if (~ic_access) begin
            ibus_req_r <= 1'b1;
            ibus_adr_r <= s2t_phys_addr_mux;
            state      <= READ;
          end
          else if (ic_refill_req) begin
            ibus_req_r <= 1'b1;
            ibus_adr_r <= s2t_phys_addr_mux;
            state      <= IC_REFILL;
          end
        end // new address taken & cache off/miss & no exceptions
      end // idle

      IC_REFILL: begin
        ibus_req_r <= 1'b1;
        if (ibus_ack_i) begin
          ibus_adr_r <= next_ibus_adr;
          if (ic_refill_done) begin
            ibus_req_r <= 1'b0;
            state      <= IDLE;
          end
        end
        if (ibus_err_i) begin
          ibus_req_r <= 1'b0;
          state      <= IDLE;
        end
      end // ic-refill

      READ: begin
        ibus_req_r <= 1'b1;
        if (ibus_ack_i | ibus_err_i) begin
          ibus_req_r <= 1'b0;
          state      <= IDLE;
        end
      end // read

      default: begin
        ibus_req_r <= 1'b0;
        state      <= IDLE;
      end // not defined
    endcase // case (state)

    if (rst) begin
      ibus_req_r <= 1'b0;
      state      <= IDLE;
    end
  end // @ clock

  // to WBUS bridge
  assign ibus_adr_o   = ibus_adr_r;
  assign ibus_req_o   = ibus_req_r;
  assign ibus_burst_o = (state == IC_REFILL) & ic_refill & ~ic_refill_done;

  //---------------//
  // SPR interface //
  //---------------//

  //   For MAROCCHINO SPR access means that pipeline is stalled till ACK.
  // So, no padv-*. We only delay SPR access command till IBUS transaction
  // completion.

  //   Delay ACK by 1-clock to be sync-ed with invalidation
  // process implemented in current ICACHE implementation
  reg    spr_bus_ack_ic_r;
  assign spr_bus_ack_ic_o = spr_bus_ack_ic_r;

  // request access to ICACHE
  wire spr_bus_ic_stb   = spr_bus_stb_i & (spr_bus_addr_i == `OR1K_SPR_ICBIR_ADDR);
  // request access to IMMU
  wire spr_bus_immu_stb = spr_bus_stb_i & (spr_bus_addr_i[15:11] == 5'd2);

  // flag to rise spr-bus-ic(immu)-cs-r
  assign assert_spr_bus_req = ((spr_bus_ic_stb & ~spr_bus_ic_cs_r & ~spr_bus_ack_ic_r) |
                               (spr_bus_immu_stb & ~spr_bus_immu_cs_r)) & ~stall_s1;

  // IMMU SPR access processing
  // provide STB-signal after IBUS transaction completion
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      spr_bus_immu_cs_r <= 1'b0;
    // Drop flags after SPR access completion
    else if (spr_bus_immu_cs_r & spr_bus_ack_immu_o)
      spr_bus_immu_cs_r <= 1'b0;
    // provide STB-signal to IMMU
    else if (assert_spr_bus_req)
      spr_bus_immu_cs_r <= spr_bus_immu_stb;
  end // @ clock

  // ICACHE SPR access processing
  wire   spr_bus_ack_ic; // connection to ICACHE
  // ----
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      spr_bus_ic_cs_r   <= 1'b0;
      spr_bus_ack_ic_r  <= 1'b0;
    end
    // The delayed ACK drops SPR request fom EXECUTE at next posedge clock
    else if (spr_bus_ack_ic_r) begin
      spr_bus_ic_cs_r   <= 1'b0;
      spr_bus_ack_ic_r  <= 1'b0;
    end
    // Drop request flags and 1-clock delay for ACK to EXECUTE
    else if (spr_bus_ic_cs_r & spr_bus_ack_ic) begin
      spr_bus_ic_cs_r   <= 1'b0;
      spr_bus_ack_ic_r  <= 1'b1;
    end
    // provide STB-signal to ICACHE
    else if (assert_spr_bus_req) begin
      spr_bus_ic_cs_r  <= spr_bus_ic_stb;
      spr_bus_ack_ic_r <= 1'b0;
    end
  end // @ clock

  //-------------------//
  // Instance of cache //
  //-------------------//

generate
  //   Hack? Work around MMU?
  // Today the thing is actual for DCACHE only.
  // Addresses 0x8******* are treated as non-cacheble regardless MMU's flag.

  // MAROCCHINO_TODO:
  //   The ic_check_limit_width usage isn't harmonized with IMMU on/off.
  // On the other hand it isn't problem for FETCH because
  // ic_check_limit_width == 1 thanks to setting of
  // OPTION_ICACHE_LIMIT_WIDTH == OPTION_OPERAND_WIDTH from instance of mor1kx.

  if (OPTION_ICACHE_LIMIT_WIDTH == OPTION_OPERAND_WIDTH)
    assign ic_check_limit_width = 1'b1;
  else if (OPTION_ICACHE_LIMIT_WIDTH < OPTION_OPERAND_WIDTH)
    assign ic_check_limit_width =
      (s2t_phys_addr_mux[OPTION_OPERAND_WIDTH-1:OPTION_ICACHE_LIMIT_WIDTH] == 0);
  else begin
    initial begin
      $display("ERROR: OPTION_ICACHE_LIMIT_WIDTH > OPTION_OPERAND_WIDTH");
      $finish();
    end
  end
endgenerate

  assign ic_access = ic_enabled & ic_check_limit_width & ~(immu_enabled_r & immu_cache_inhibit) & ~fetch_excepts;

  assign ic_req = ic_access & imem_req_r;

  // ICACHE output ready (by read or re-fill)
  assign ic_rdy = ic_req & ic_ack;

  mor1kx_icache
  #(
    .OPTION_ICACHE_BLOCK_WIDTH(OPTION_ICACHE_BLOCK_WIDTH),
    .OPTION_ICACHE_SET_WIDTH(OPTION_ICACHE_SET_WIDTH),
    .OPTION_ICACHE_WAYS(OPTION_ICACHE_WAYS),
    .OPTION_ICACHE_LIMIT_WIDTH(OPTION_ICACHE_LIMIT_WIDTH)
  )
  mor1kx_icache
  (
    .clk                 (clk),
    .rst                 (rst),
    // Outputs
    .refill_o            (ic_refill), // ICACHE
    .refill_req_o        (ic_refill_req), // ICACHE
    .refill_done_o       (ic_refill_done), // ICACHE
    .invalidate_o        (), // ICACHE (was: ic_invalidate) not used
    .cpu_ack_o           (ic_ack), // ICACHE
    .cpu_dat_o           (ic_dat), // ICACHE
    // Inputs
    .ic_imem_err_i       (except_ibus_err), // ICACHE
    .ic_access_i         (ic_access), // ICACHE
    .cpu_adr_i           (s1t_pc_mux), // ICACHE (was: ic_addr)
    .cpu_adr_match_i     (s2t_phys_addr_mux), // ICACHE (was: ic_addr_match)
    .cpu_req_i           (ic_req), // ICACHE
    .wradr_i             (ibus_adr_r), // ICACHE (was: ibus_adr)
    .wrdat_i             (ibus_dat_i), // ICACHE
    .we_i                (ibus_ack_i), // ICACHE
    // SPR bus
    .spr_bus_addr_i      (spr_bus_addr_i[15:0]), // ICACHE
    .spr_bus_we_i        (spr_bus_we_i), // ICACHE
    .spr_bus_stb_i       (spr_bus_ic_cs_r), // ICACHE
    .spr_bus_dat_i       (spr_bus_dat_i), // ICACHE
    .spr_bus_dat_o       (spr_bus_dat_ic_o), // ICACHE
    .spr_bus_ack_o       (spr_bus_ack_ic) // ICACHE
  );

  //------------------//
  // Instance of IMMU //
  //------------------//

  // connections to IMMU module
  wire immu_tlb_miss;
  wire immu_pagefault;

  // Block IMMU exceptions for "next to delay slot instruction"
  // and mispredict cases.
  wire immu_excepts_enabled = immu_enabled_r & ~flush_by_branch & ~flush_by_mispredict;

  // IMMU exceptions with enable
  assign except_itlb_miss  = immu_tlb_miss  & immu_excepts_enabled;
  assign except_ipagefault = immu_pagefault & immu_excepts_enabled;
  assign immu_an_except    = (immu_tlb_miss | immu_tlb_miss) & immu_excepts_enabled;

  mor1kx_immu
  #(
    .FEATURE_IMMU_HW_TLB_RELOAD(FEATURE_IMMU_HW_TLB_RELOAD),
    .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH),
    .OPTION_IMMU_SET_WIDTH(OPTION_IMMU_SET_WIDTH),
    .OPTION_IMMU_WAYS(OPTION_IMMU_WAYS)
  )
  mor1kx_immu
  (
    .clk                            (clk),
    .rst                            (rst),
    // Controls
    .enable_i                       (immu_enabled_r), // IMMU
    .supervisor_mode_i              (immu_svmode_r), // IMMU
    // Inputs addresses
    .virt_addr_i                    (s1t_pc_mux), // IMMU (was: ic_addr)
    .virt_addr_match_i              (s1o_virt_addr), // IMMU (was: pc_fetch)
    // Outputs
    .phys_addr_o                    (immu_phys_addr), // IMMU
    .cache_inhibit_o                (immu_cache_inhibit), // IMMU
    .tlb_miss_o                     (immu_tlb_miss), // IMMU (was: tlb_miss)
    .pagefault_o                    (immu_pagefault), // IMMU (was: pagefault)
    .busy_o                         (), // IMMU (was: immu_busy) not used
    // TLB HW reload face. MAROCCHINO_TODO: not implemented
    .tlb_reload_ack_i               (1'b0), // IMMU
    .tlb_reload_data_i              ({OPTION_OPERAND_WIDTH{1'b0}}), // IMMU
    .tlb_reload_pagefault_clear_i   (1'b0), // IMMU
    .tlb_reload_req_o               (), // IMMU
    .tlb_reload_addr_o              (), // IMMU
    .tlb_reload_pagefault_o         (), // IMMU
    .tlb_reload_busy_o              (), // IMMU
    // SPR bus face
    .spr_bus_addr_i                 (spr_bus_addr_i[15:0]), // IMMU
    .spr_bus_we_i                   (spr_bus_we_i), // IMMU
    .spr_bus_stb_i                  (spr_bus_immu_cs_r), // IMMU
    .spr_bus_dat_i                  (spr_bus_dat_i), // IMMU
    .spr_bus_dat_o                  (spr_bus_dat_immu_o), // IMMU
    .spr_bus_ack_o                  (spr_bus_ack_immu_o) // IMMU
  );

endmodule // mor1kx_fetch_marocchino
