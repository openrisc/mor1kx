////////////////////////////////////////////////////////////////////////
//                                                                    //
//  mor1kx_icache_marocchino                                          //
//                                                                    //
//  Description: mor1kx fetch/address stage unit                      //
//               for MAROCCHINO pipeline                              //
//               basically an interface to the ibus/icache subsystem  //
//               that can react to exception and branch signals       //
//                                                                    //
//               refactored version of mor1kx_fetch_cappuccino        //
//                                                                    //
////////////////////////////////////////////////////////////////////////
//                                                                    //
//   Copyright (C) 2012  Julius Baxter                                //
//                       juliusbaxter@gmail.com                       //
//                                                                    //
//                       Stefan Kristiansson                          //
//                       stefan.kristiansson@saunalahti.fi            //
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

module mor1kx_fetch_marocchino
#(
  parameter OPTION_OPERAND_WIDTH        = 32,
  parameter OPTION_RESET_PC             = {{(OPTION_OPERAND_WIDTH-13){1'b0}},
                                           `OR1K_RESET_VECTOR,8'd0},
  parameter OPTION_RF_ADDR_WIDTH        =  5,
  // cache configuration
  parameter OPTION_ICACHE_BLOCK_WIDTH   =  5,
  parameter OPTION_ICACHE_SET_WIDTH     =  9,
  parameter OPTION_ICACHE_WAYS          =  2,
  parameter OPTION_ICACHE_LIMIT_WIDTH   = 32,
  parameter OPTION_ICACHE_CLEAR_ON_INIT =  0,
  // mmu configuration
  parameter FEATURE_IMMU_HW_TLB_RELOAD  = "NONE",
  parameter OPTION_IMMU_SET_WIDTH       =  6,
  parameter OPTION_IMMU_WAYS            =  1,
  parameter OPTION_IMMU_CLEAR_ON_INIT   =  0
)
(
  // clock and reset
  input                                 clk,
  input                                 rst,

  // pipeline control
  input                                 padv_fetch_i,
  input                                 fetch_waiting_target_i,
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
  output reg                            ibus_req_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] ibus_adr_o,
  output                                ibus_burst_o,

  // branch/jump control transfer
  //  ## detect jump/branch to indicate "delay slot" for next fetched instruction
  input                                 dcod_jump_or_branch_i,
  //  ## do branch (pedicted or unconditional)
  input                                 dcod_do_branch_i,
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_do_branch_target_i,

  // DU/exception/rfe control transfer
  input                                 ctrl_branch_exception_i,
  input      [OPTION_OPERAND_WIDTH-1:0] ctrl_branch_except_pc_i,

  // to RF
  output                                fetch_rf_adr_valid_o,
  output     [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfa1_adr_o,
  output     [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfb1_adr_o,
  // for FPU64
  output     [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfa2_adr_o,
  output     [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfb2_adr_o,

  // to DECODE
  output reg                            dcod_insn_valid_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] pc_decode_o,
  output reg     [`OR1K_INSN_WIDTH-1:0] dcod_insn_o,
  output reg                            dcod_delay_slot_o,
  output     [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa1_adr_o,
  output     [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb1_adr_o,
  // for FPU64
  output     [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa2_adr_o,
  output     [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb2_adr_o,
  output     [OPTION_RF_ADDR_WIDTH-1:0] insn_rfd2_adr_o,

  // exceptions
  output reg                            fetch_except_ibus_err_o,
  output reg                            fetch_except_itlb_miss_o,
  output reg                            fetch_except_ipagefault_o,
  output reg                            fetch_an_except_o,
  output reg                            fetch_exception_taken_o
);

  /*
     Definitions:
       s??o_name - "S"tage number "??", "O"utput
       s??t_name - "S"tage number "??", "T"emporary (internally)
  */

  localparam IFOOW = OPTION_OPERAND_WIDTH; // short name

  /* MMU related controls and signals */

  // IMMU's regular output
  wire                            immu_cache_inhibit;
  // IMMU exceptions (valid for enabled mmu only)
  wire                            except_itlb_miss;
  wire                            except_ipagefault;
  /* HW reload TLB related (MAROCCHINO_TODO : not implemented yet)
  wire                            tlb_reload_req;
  reg                             tlb_reload_ack;
  wire                [IFOOW-1:0] tlb_reload_addr;
  reg                 [IFOOW-1:0] tlb_reload_data;
  wire                            tlb_reload_pagefault;
  wire                            tlb_reload_busy; */


  /* ICACHE related controls and signals */

  // ICACHE access flag (without taking exceptions into accaunt)
  wire                            ic_access;
  // ICACHE output ready (by read or re-fill) and data
  wire                            ic_ack;
  wire     [`OR1K_INSN_WIDTH-1:0] ic_dat;
  // ICACHE requests and performs refill
  wire                            ic_refill_req;
  wire                [IFOOW-1:0] next_refill_adr;
  wire                            ic_refill_first;
  wire                            ic_refill_last;


  /* IBUS access state machine controls */

  //   IBUS output ready
  // Indicates IBUS ACK for IBUS direct access only
  // (not ACKs for ICACHE refill):
  wire              ibus_ack;
  // IBUS FSM statuses
  wire              ibus_fsm_free;
  // IBUS access state machine
  localparam  [3:0] IBUS_IDLE       = 4'b0001,
                    IMEM_REQ        = 4'b0010,
                    IBUS_READ       = 4'b0100,
                    IBUS_IC_REFILL  = 4'b1000;
  // ---
  reg         [3:0] ibus_state;
  // particular states
  wire              ibus_idle_state = ibus_state[0];
  wire              imem_req_state  = ibus_state[1];
  wire              ibus_read_state = ibus_state[2];
  wire              ic_refill_state = ibus_state[3];
  // IBUS error processing
  wire              ibus_err_instant; // error reported "just now"
  reg               except_ibus_err;  // masked by stage #2 flushing (see later)


  /* ICACHE/IBUS requests and nswers */

  // The logic is located in Stage #2 section

  // ACK/DATA pending till next IFETCH advance
  reg                         imem_ack_p;
  reg  [`OR1K_INSN_WIDTH-1:0] imem_dat_p;


  /* Wires & registers are used across FETCH pipe stages */

  // Flush processing
  wire flush_by_ctrl;    // flush registers from pipeline-flush command till IBUS transaction completion

  // ICACHE/IMMU match address store register
  //   The register operates in the same way
  // as memory blocks in ICACHE/IMMU to provide correct
  // address for comparision on output of ICACHE/MMU memory blocks.
  reg  [IFOOW-1:0] virt_addr_fetch;

  // Physical address (after translation in IMMU)
  wire [IFOOW-1:0] phys_addr_fetch;

  // to s3:
  reg [IFOOW-1:0] s2o_pc; // program counter
  reg             s2o_ds; // delay slot is in stage #3 (on stage #2 output)


  /************************/
  /* IFETCH pipe controls */
  /************************/

  // Advance stage #1
  wire padv_s1 = padv_fetch_i & ibus_fsm_free;


  /********************/
  /* IFETCH exeptions */
  /********************/

  // IBUS error during IBUS access
  assign ibus_err_instant = ibus_req_o & ibus_err_i;
  // IBUS error pending
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      except_ibus_err <= 1'b0;
    else if (padv_s1 | flush_by_ctrl)
      except_ibus_err <= 1'b0;
    else if (ibus_err_instant)
      except_ibus_err <= 1'b1;
  end // @ clock

  // combined MMU's and IBUS's exceptions
  wire immu_an_except  = (except_itlb_miss | except_ipagefault);
  wire fetch_an_except = (immu_an_except   | except_ibus_err);


  /************************************************/
  /* Stage #1: PC update and IMMU / ICACHE access */
  /************************************************/

  // detector that stage #1 is fetching next instruction:
  //   PC in DECODE and IFETCH differs by 4
  wire s1_fetching_next_insn = virt_addr_fetch[2] ^ pc_decode_o[2];

  // pending "fetch delay slot" till next padv-s1
  reg fetch_ds_p;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      fetch_ds_p <= 1'b0;
    else if (padv_s1 | flush_by_ctrl)
      fetch_ds_p <= 1'b0;
    else if (~fetch_ds_p)
      fetch_ds_p <= (dcod_jump_or_branch_i & ~s1_fetching_next_insn);
  end // @ clock
  // ---
  wire fetch_ds_next = (dcod_jump_or_branch_i & ~s1_fetching_next_insn) | fetch_ds_p;

  //  flag to indicate that ICACHE/IBUS is fetchinng delay slot
  // fetching delay slot
  reg fetching_ds_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      fetching_ds_r <= 1'b0;
    else if (flush_by_ctrl)
      fetching_ds_r <= 1'b0;
    else if (padv_s1)
      fetching_ds_r <= fetch_ds_next;
    else if (~fetching_ds_r)
      fetching_ds_r <= (dcod_jump_or_branch_i & s1_fetching_next_insn);
  end // @ clock
  // combined fetching delay slot flag
  wire fetching_ds = (dcod_jump_or_branch_i & s1_fetching_next_insn) | fetching_ds_r;


  // store branch flag and target if stage #1 is busy
  reg             dcod_do_branch_p;
  reg [IFOOW-1:0] dcod_do_branch_target_p;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      dcod_do_branch_p <= 1'b0; // reset
    else if ((padv_s1 & ~fetch_ds_next) | flush_by_ctrl)  // for clean up stored branch
      dcod_do_branch_p <= 1'b0; // take stored branch or flush by pipe-flushing
    else if (dcod_do_branch_i & ~fetch_waiting_target_i & ~dcod_do_branch_p) begin
      dcod_do_branch_p        <= 1'b1;
      dcod_do_branch_target_p <= dcod_do_branch_target_i;
    end
  end // @ clock


  // 1-clock fetch-exception-taken
  // The flush-by-ctrl is dropped synchronously with s1-stall
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      fetch_exception_taken_o <= 1'b0;
    else if (fetch_exception_taken_o | flush_by_ctrl)
      fetch_exception_taken_o <= 1'b0;
    else if (padv_s1 & ctrl_branch_exception_i)
      fetch_exception_taken_o <= 1'b1;
  end // @ clock


  // regular value of next PC
  wire [IFOOW-1:0] virt_addr_next = virt_addr_fetch + 3'd4;

  // Select the PC for next fetch
  wire [IFOOW-1:0] virt_addr_mux =
    // Use DU/exceptions/rfe provided address
    (ctrl_branch_exception_i & ~fetch_exception_taken_o) ? ctrl_branch_except_pc_i :
    // regular update of IFETCH
    fetch_ds_next                                        ? virt_addr_next          :
    dcod_do_branch_p                                     ? dcod_do_branch_target_p :
    dcod_do_branch_i                                     ? dcod_do_branch_target_i :
                                                           virt_addr_next;


  // ICACHE/IMMU match address store register
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      virt_addr_fetch <= OPTION_RESET_PC - 4; // will be restored on 1st advance
    else if (padv_s1 & ~flush_by_ctrl)
      virt_addr_fetch <= virt_addr_mux;
  end // @ clock


  /****************************************/
  /* Stage #2: ICACHE check / IBUS access */
  /****************************************/


  //----------------------------------------//
  // IBUS/ICACHE <-> FETCH's pipe interface //
  //----------------------------------------//

  // ACK and DATA from IBUS/ICAHCE stored till nearest advance
  //  # ACK
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      imem_ack_p <= 1'b0;
    else if (padv_fetch_i | flush_by_ctrl)
      imem_ack_p <= 1'b0;
    else if (ic_ack | ibus_ack)
      imem_ack_p <= 1'b1;
  end // @ clock
  //  # ICACHE
  always @(posedge clk) begin
    if (ic_ack)
      imem_dat_p <= ic_dat;
    else if (ibus_ack)
      imem_dat_p <= ibus_dat_i;
  end // @ clock


  //-------------------------------------------//
  // Stage #2 output latches (output of FETCH) //
  //-------------------------------------------//

  // not masked combination of ACKs
  wire s2t_ack = ic_ack | ibus_ack | imem_ack_p;

  // valid instruction
  wire s2t_insn_or_excepts = s2t_ack | fetch_an_except;

  // instruction word
  wire [`OR1K_INSN_WIDTH-1:0] s2t_insn_mux =
    fetch_an_except ? {`OR1K_OPCODE_NOP,26'd0} :
    ic_ack          ? ic_dat                   :
    ibus_ack        ? ibus_dat_i               :
    imem_ack_p      ? imem_dat_p               :
                      {`OR1K_OPCODE_NOP,26'd0};

  // to DECODE: delay slot flag
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      dcod_delay_slot_o         <= 1'b0;
      dcod_insn_o               <= {`OR1K_OPCODE_NOP,26'd0};
      dcod_insn_valid_o         <= 1'b0;
      // exceptions
      fetch_except_ibus_err_o   <= 1'b0;
      fetch_except_itlb_miss_o  <= 1'b0;
      fetch_except_ipagefault_o <= 1'b0;
      fetch_an_except_o         <= 1'b0;
      // actual programm counter
      pc_decode_o               <= {IFOOW{1'b0}}; // reset
    end
    else if (flush_by_ctrl) begin
      dcod_delay_slot_o         <= 1'b0;
      dcod_insn_o               <= {`OR1K_OPCODE_NOP,26'd0};
      dcod_insn_valid_o         <= 1'b0;
      // exceptions
      fetch_except_ibus_err_o   <= 1'b0;
      fetch_except_itlb_miss_o  <= 1'b0;
      fetch_except_ipagefault_o <= 1'b0;
      fetch_an_except_o         <= 1'b0;
      // actual programm counter
      pc_decode_o               <= {IFOOW{1'b0}}; // flush
    end
    else if (padv_fetch_i) begin
      dcod_delay_slot_o         <= fetching_ds & s2t_insn_or_excepts;
      dcod_insn_o               <= s2t_insn_mux;
      dcod_insn_valid_o         <= s2t_insn_or_excepts; // valid instruction or exception
      // exceptions
      fetch_except_ibus_err_o   <= except_ibus_err;
      fetch_except_itlb_miss_o  <= except_itlb_miss;
      fetch_except_ipagefault_o <= except_ipagefault;
      fetch_an_except_o         <= fetch_an_except;
      // actual programm counter
      pc_decode_o               <= virt_addr_fetch;
    end
  end // @ clock

  // read operands from RF
  assign fetch_rf_adr_valid_o = padv_fetch_i;// & s2t_ack & ~flush_by_ctrl; // MAROCCHINO_TODO: remove extra logic?

  // to RF
  assign fetch_rfa1_adr_o = s2t_insn_mux[`OR1K_RA_SELECT];
  assign fetch_rfb1_adr_o = s2t_insn_mux[`OR1K_RB_SELECT];

  // to DECODE
  assign dcod_rfa1_adr_o = dcod_insn_o[`OR1K_RA_SELECT];
  assign dcod_rfb1_adr_o = dcod_insn_o[`OR1K_RB_SELECT];

  // to FPU64
  assign fetch_rfa2_adr_o = s2t_insn_mux[`OR1K_RA_SELECT] + 1'b1;
  assign fetch_rfb2_adr_o = s2t_insn_mux[`OR1K_RB_SELECT] + 1'b1;
  // ---
  reg [(OPTION_RF_ADDR_WIDTH-1):0] dcod_rfa2_adr_r, dcod_rfb2_adr_r, insn_rfd2_adr_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      dcod_rfa2_adr_r <= {{(OPTION_RF_ADDR_WIDTH-1){1'b0}},1'b1};
      dcod_rfb2_adr_r <= {{(OPTION_RF_ADDR_WIDTH-1){1'b0}},1'b1};
      insn_rfd2_adr_r <= {{(OPTION_RF_ADDR_WIDTH-1){1'b0}},1'b1};
    end
    else if (flush_by_ctrl) begin
      dcod_rfa2_adr_r <= {{(OPTION_RF_ADDR_WIDTH-1){1'b0}},1'b1};
      dcod_rfb2_adr_r <= {{(OPTION_RF_ADDR_WIDTH-1){1'b0}},1'b1};
      insn_rfd2_adr_r <= {{(OPTION_RF_ADDR_WIDTH-1){1'b0}},1'b1};
    end
    else if (padv_fetch_i) begin
      dcod_rfa2_adr_r <= fetch_rfa2_adr_o;
      dcod_rfb2_adr_r <= fetch_rfb2_adr_o;
      insn_rfd2_adr_r <= s2t_insn_mux[`OR1K_RD_SELECT] + 1'b1;
    end
  end // @ clock
  // ---
  assign dcod_rfa2_adr_o = dcod_rfa2_adr_r;
  assign dcod_rfb2_adr_o = dcod_rfb2_adr_r;
  assign insn_rfd2_adr_o = insn_rfd2_adr_r;


  /********** End of FETCH pipe. Start other logics. **********/

  //-------------//
  // Flush logic //
  //-------------//

  // store flush command till IBUS transactions complete
  reg flush_r;
  // ----
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      flush_r <= 1'b0;
    else if (ibus_fsm_free)
      flush_r <= 1'b0;
    else if (~flush_r)
      flush_r <= pipeline_flush_i;
  end // @ clock

  // combination of pipeline-flush and flush-r
  assign flush_by_ctrl = pipeline_flush_i | flush_r;

  //--------------------//
  // IBUS state machine //
  //--------------------//

  // IBUS FSM status is stop
  // !!! should follows appropriate FSM condition,
  //     but without taking into account exceptions
  assign ibus_fsm_free = ibus_idle_state                | // IBUS FSM is free
                         (imem_req_state  & ic_ack)     | // IBUS FSM is free
                         (ibus_read_state & ibus_ack_i);  // IBUS FSM is free

  // IBUS output ready (no bus error case)
  //  (a) read none-cached area
  //  (b) 1-st data during cache re-fill
  assign ibus_ack = ((ibus_read_state | (ic_refill_state & ic_refill_first)) & ibus_ack_i);


  // state machine itself
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      ibus_req_o <= 1'b0;           // by reset
      ibus_adr_o <= {IFOOW{1'b0}};  // by reset
      ibus_state <= IBUS_IDLE;      // by reset
    end
    else if (ibus_err_instant) begin // IBUS FSM
      ibus_req_o <= 1'b0;           // by IBUS error
      ibus_adr_o <= {IFOOW{1'b0}};  // by IBUS error
      ibus_state <= IBUS_IDLE;      // by IBUS error
    end
    else begin
      // synthesis parallel_case full_case
      case (ibus_state)
        IBUS_IDLE: begin
          if (flush_by_ctrl)
            ibus_state <= IBUS_IDLE; // idling -> keep by exceptions or flushing
          else if (padv_fetch_i) // eq. padv_s1 (in IDLE state of IBUS FSM)
            ibus_state <= IMEM_REQ;  // idling -> memory system request
        end

        IMEM_REQ: begin
          if (immu_an_except | flush_by_ctrl) begin
            ibus_state <= IBUS_IDLE;  // memory system request -> idling (exceptions or flushing)
          end
          else if (padv_fetch_i & ic_ack) begin // eq. padv_s1 (in IMEM-REQ state of IBUS FSM)
            ibus_state <= IMEM_REQ;  // keep memory system request
          end
          else if (ic_refill_req) begin
            ibus_req_o <= 1'b1;             // memory system request -> ICACHE refill
            ibus_adr_o <= phys_addr_fetch;  // memory system request -> ICACHE refill
            ibus_state <= IBUS_IC_REFILL;   // memory system request -> ICACHE refill
          end
          else if (~ic_access) begin
            ibus_req_o <= 1'b1;             // memory system request -> IBUS read
            ibus_adr_o <= phys_addr_fetch;  // memory system request -> IBUS read
            ibus_state <= IBUS_READ;        // memory system request -> IBUS read
          end
          else
            ibus_state <= IBUS_IDLE;
        end

        IBUS_IC_REFILL: begin
          if (ibus_ack_i) begin
            ibus_adr_o <= next_refill_adr;  // ICACHE refill: next address
            if (ic_refill_last) begin
              ibus_req_o <= 1'b0;           // ICACHE refill -> idling
              ibus_adr_o <= {IFOOW{1'b0}};  // ICACHE refill -> idling
              ibus_state <= IBUS_IDLE;      // ICACHE refill -> idling
            end
          end
        end // ic-refill

        IBUS_READ: begin
          if (ibus_ack_i) begin
            ibus_req_o <= 1'b0;                 // IBUS read: complete
            ibus_adr_o <= {IFOOW{1'b0}};        // IBUS read: complete
            if (padv_fetch_i & ~flush_by_ctrl)  // IBUS read -> IMEM REQUEST (eq. padv_s1)
              ibus_state <= IMEM_REQ;           // IBUS read -> IMEM REQUEST
            else
              ibus_state <= IBUS_IDLE;          // IBUS READ -> IDLE
          end
        end // read

        default: begin
          ibus_req_o <= 1'b0;           // default
          ibus_adr_o <= {IFOOW{1'b0}};  // default
          ibus_state <= IBUS_IDLE;      // default
        end
      endcase // case (state)
    end // reset / regular update
  end // @ clock

  // And burst mode
  assign ibus_burst_o = (ic_refill_state & ~ic_refill_last);


  //---------------//
  // SPR interface //
  //---------------//

  //   For MAROCCHINO SPR access means that pipeline is stalled till ACK.
  // So, no padv-*. We only delay SPR access command till IBUS transaction
  // completion.
  wire spr_bus_stb_ifetch = (ibus_idle_state & spr_bus_stb_i);



  //-------------------//
  // Instance of cache //
  //-------------------//

  // ICACHE module
  mor1kx_icache_marocchino
  #(
    .OPTION_OPERAND_WIDTH         (OPTION_OPERAND_WIDTH), // ICACHE
    .OPTION_ICACHE_BLOCK_WIDTH    (OPTION_ICACHE_BLOCK_WIDTH), // ICACHE
    .OPTION_ICACHE_SET_WIDTH      (OPTION_ICACHE_SET_WIDTH), // ICACHE
    .OPTION_ICACHE_WAYS           (OPTION_ICACHE_WAYS), // ICACHE
    .OPTION_ICACHE_LIMIT_WIDTH    (OPTION_ICACHE_LIMIT_WIDTH), // ICACHE
    .OPTION_ICACHE_CLEAR_ON_INIT  (OPTION_ICACHE_CLEAR_ON_INIT) // ICACHE
  )
  u_icache
  (
    // clock and reset
    .clk                  (clk), // ICACHE
    .rst                  (rst), // ICACHE
    // pipe controls
    .padv_s1_i            (padv_s1), // ICACHE
    .flush_by_ctrl_i      (flush_by_ctrl), // ICACHE
    // fetch exceptions
    .immu_an_except_i     (immu_an_except), // ICACHE
    .ibus_err_i           (ibus_err_i), // ICACHE: cancel re-fill
    // configuration
    .enable_i             (ic_enable_i), // ICACHE
    // regular requests in/out
    .virt_addr_mux_i      (virt_addr_mux), // ICACHE
    .phys_addr_fetch_i    (phys_addr_fetch), // ICACHE
    .immu_cache_inhibit_i (immu_cache_inhibit), // ICACHE
    .ic_access_o          (ic_access), // ICACHE
    .ic_ack_o             (ic_ack), // ICACHE
    .ic_dat_o             (ic_dat), // ICACHE
    // re-fill
    .refill_req_o         (ic_refill_req), // ICACHE
    .ic_refill_allowed_i  (imem_req_state), // ICACHE
    .next_refill_adr_o    (next_refill_adr), // ICACHE
    .ic_refill_first_o    (ic_refill_first), // ICACHE
    .ic_refill_last_o     (ic_refill_last), // ICACHE
    .ibus_dat_i           (ibus_dat_i), // ICACHE
    .ibus_ack_i           (ibus_ack_i), // ICACHE
    // SPR bus
    .spr_bus_addr_i       (spr_bus_addr_i[15:0]), // ICACHE
    .spr_bus_we_i         (spr_bus_we_i), // ICACHE
    .spr_bus_stb_i        (spr_bus_stb_ifetch), // ICACHE
    .spr_bus_dat_i        (spr_bus_dat_i), // ICACHE
    .spr_bus_dat_o        (spr_bus_dat_ic_o), // ICACHE
    .spr_bus_ack_o        (spr_bus_ack_ic_o) // ICACHE
  );


  //------------------//
  // Instance of IMMU //
  //------------------//

  mor1kx_immu_marocchino
  #(
    .FEATURE_IMMU_HW_TLB_RELOAD     (FEATURE_IMMU_HW_TLB_RELOAD), // IMMU
    .OPTION_OPERAND_WIDTH           (OPTION_OPERAND_WIDTH), // IMMU
    .OPTION_RESET_PC                (OPTION_RESET_PC), // IMMU
    .OPTION_IMMU_SET_WIDTH          (OPTION_IMMU_SET_WIDTH), // IMMU
    .OPTION_IMMU_WAYS               (OPTION_IMMU_WAYS), // IMMU
    .OPTION_IMMU_CLEAR_ON_INIT      (OPTION_IMMU_CLEAR_ON_INIT) // IMMU
  )
  u_immu
  (
    .clk                            (clk), // IMMU
    .rst                            (rst), // IMMU
    // controls
    .padv_s1_i                      (padv_s1), // IMMU
    .flush_by_ctrl_i                (flush_by_ctrl), // IMMU
    // configuration
    .enable_i                       (immu_enable_i), // IMMU
    .supervisor_mode_i              (supervisor_mode_i), // IMMU
    // address translation
    .virt_addr_mux_i                (virt_addr_mux), // IMMU
    .virt_addr_fetch_i              (virt_addr_fetch), // IMMU
    .phys_addr_fetch_o              (phys_addr_fetch), // IMMU
    // flags
    .cache_inhibit_o                (immu_cache_inhibit), // IMMU
    .tlb_miss_o                     (except_itlb_miss), // IMMU
    .pagefault_o                    (except_ipagefault), // IMMU
    // TLB HW reload face. MAROCCHINO_TODO: not implemented
    .tlb_reload_req_o               (), // IMMU
    .tlb_reload_ack_i               (1'b0), // IMMU
    .tlb_reload_addr_o              (), // IMMU
    .tlb_reload_data_i              ({OPTION_OPERAND_WIDTH{1'b0}}), // IMMU
    .tlb_reload_pagefault_o         (), // IMMU
    .tlb_reload_pagefault_clear_i   (1'b0), // IMMU
    .tlb_reload_busy_o              (), // IMMU
    // SPR bus face
    .spr_bus_addr_i                 (spr_bus_addr_i[15:0]), // IMMU
    .spr_bus_we_i                   (spr_bus_we_i), // IMMU
    .spr_bus_stb_i                  (spr_bus_stb_ifetch), // IMMU
    .spr_bus_dat_i                  (spr_bus_dat_i), // IMMU
    .spr_bus_dat_o                  (spr_bus_dat_immu_o), // IMMU
    .spr_bus_ack_o                  (spr_bus_ack_immu_o) // IMMU
  );

endmodule // mor1kx_fetch_marocchino
