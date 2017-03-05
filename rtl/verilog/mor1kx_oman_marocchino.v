/////////////////////////////////////////////////////////////////////
//                                                                 //
//  mor1kx_oman_marocchino                                         //
//                                                                 //
//  Description: mor1kx [O]rder [MAN]ager unit                     //
//               for MAROCCHINO pipeline                           //
//    a) collect various state signals from DECODE                 //
//       and EXECUTE modules                                       //
//    b) analisys of conflicts                                     //
//    c) generate valid flags for advance DECODE and WB            //
//                                                                 //
/////////////////////////////////////////////////////////////////////
//                                                                 //
//   Copyright (C) 2015 Andrey Bacherov                            //
//                      avbacherov@opencores.org                   //
//                                                                 //
//      This Source Code Form is subject to the terms of the       //
//      Open Hardware Description License, v. 1.0. If a copy       //
//      of the OHDL was not distributed with this file, You        //
//      can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt    //
//                                                                 //
/////////////////////////////////////////////////////////////////////

`include "mor1kx-defines.v"

module mor1kx_oman_marocchino
#(
  parameter OPTION_OPERAND_WIDTH = 32,
  parameter OPTION_RF_ADDR_WIDTH =  5,
  parameter DEST_REG_ADDR_WIDTH  =  8, // OPTION_RF_ADDR_WIDTH + log2(Re-Ordering buffer width)
  parameter DEST_EXT_ADDR_WIDTH  =  3  // log2(Re-Ordering buffer width)
)
(
  // clock & reset
  input                                 clk,
  input                                 rst,

  // pipeline control
  input                                 padv_decode_i,
  input                                 padv_wb_i,
  input                                 pipeline_flush_i,

  // DECODE non-latched flags to indicate next required unit
  // (The information is stored in order control buffer)
  input                                 dcod_op_pass_exec_i,
  input                                 dcod_jump_or_branch_i, // just to support IBUS error handling in CTRL
  input                                 dcod_op_1clk_i,
  input                                 dcod_op_div_i,
  input                                 dcod_op_mul_i,
  input                                 dcod_op_fpxx_arith_i,
  input                                 dcod_op_ls_i,     // load / store (we need store for pushing LSU exceptions)
  input                                 dcod_op_rfe_i,    // l.rfe
  // for FPU3264
  input                                 dcod_op_fp64_arith_i,
  input                                 dcod_op_fp64_cmp_i,

  // DECODE non-latched additional information related instruction
  //  part #1: iformation stored in order control buffer
  input      [OPTION_OPERAND_WIDTH-1:0] pc_decode_i,            // instruction virtual address
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfd1_adr_i,        // WB address
  input                                 dcod_rfd1_wb_i,         // instruction generates WB
  input                                 dcod_carry_wb_i,        // instruction affects carry flag
  input                                 dcod_flag_wb_mcycle_i,  // the multy-cycle instruction affects comparison flag
  input                                 dcod_flag_wb_i,         // any instruction which affects comparison flag
  input                                 dcod_delay_slot_i,      // instruction is in delay slot
  //            for FPU64
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfd2_adr_i,        // WB2 address
  //  part #2: information required for data dependancy detection
  input                                 dcod_rfa1_req_i,    // instruction requires operand A
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa1_adr_i,    // source of operand A
  input                                 dcod_rfb1_req_i,    // instruction requires operand B
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb1_adr_i,    // source of operand B
  //  part #3: information required for create enable for
  //           for external (timer/ethernet/uart/etc) interrupts
  input                                 dcod_op_lsu_store_i,
  input                                 dcod_op_mtspr_i,
  input                                 dcod_op_msync_i,
  //  part #4: for MF(T)SPR processing
  input                                 dcod_op_mfspr_i,
  //  part #5: for FPU64, data dependancy detection
  input                                 dcod_rfa2_req_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa2_adr_i,
  input                                 dcod_rfb2_req_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb2_adr_i,

  // collect busy flags from execution modules
  input                                 op_1clk_busy_i,
  input                                 mclk_busy_i,
  input                                 lsu_busy_i,
  input                                 wb_lsu_valid_miss_i,
  input                                 wb_rfd1_wb_lsu_miss_i,
  input                                 wb_flag_wb_lsu_miss_i,

  // collect valid flags from execution modules
  input                                 exec_op_1clk_i,
  input                                 div_valid_i,
  input                                 mul_valid_i,
  input                                 fpxx_arith_valid_i,
  input                                 exec_op_fp64_cmp_i,
  input                                 lsu_valid_i,

  // D1 related WB-to-DECODE hazards for LSU WB miss processing
  input                                 dcod_wb2dec_eq_adr_d1a1_i,
  input                                 dcod_wb2dec_eq_adr_d1b1_i,
  input                                 dcod_wb2dec_eq_adr_d1a2_i,
  input                                 dcod_wb2dec_eq_adr_d1b2_i,

  // FETCH & DECODE exceptions
  input                                 fetch_except_ibus_err_i,
  input                                 fetch_except_ipagefault_i,
  input                                 fetch_except_itlb_miss_i,
  input                                 fetch_an_except_i,
  input                                 dcod_except_illegal_i,
  input                                 dcod_except_syscall_i,
  input                                 dcod_except_trap_i,

  // OMAN-to-DECODE hazards
  //  combined flag
  output                                omn2dec_a_hazard_lsu_o,
  output                                omn2dec_a_hazard_1clk_o,
  output                                omn2dec_a_hazard_mclk_o,
  //  by operands
  output                                busy_hazard_d1a1_o,
  output      [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d1a1_adr_o,
  output                                busy_hazard_d1b1_o,
  output      [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d1b1_adr_o,
  output                                busy_hazard_d2a1_o,
  output      [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d2a1_adr_o,
  output                                busy_hazard_d2b1_o,
  output      [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d2b1_adr_o,
  output                                busy_hazard_d1a2_o,
  output      [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d1a2_adr_o,
  output                                busy_hazard_d1b2_o,
  output      [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d1b2_adr_o,
  output                                busy_hazard_d2a2_o,
  output      [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d2a2_adr_o,
  output                                busy_hazard_d2b2_o,
  output      [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d2b2_adr_o,

  // EXEC-to-DECODE hazards
  //  combined flag
  output                                exe2dec_a_hazard_lsu_o,
  output                                exe2dec_a_hazard_1clk_o,
  output                                exe2dec_a_hazard_mclk_o,
  //  by operands
  output                                exe2dec_hazard_d1a1_o,
  output                                exe2dec_hazard_d1b1_o,
  output                                exe2dec_hazard_d2a1_o,
  output                                exe2dec_hazard_d2b1_o,
  output                                exe2dec_hazard_d1a2_o,
  output                                exe2dec_hazard_d1b2_o,
  output                                exe2dec_hazard_d2a2_o,
  output                                exe2dec_hazard_d2b2_o,
  // Data for resolving hazards by passing from DECODE to EXECUTE
  output                                exec_rfd1_wb_o,
  output                                exec_rfd2_wb_o,
  output      [DEST_EXT_ADDR_WIDTH-1:0] exec_ext_adr_o,

  // Stall fetch by specific type of hazards
  output reg                            oman_fd_an_except_o,

  // DECODE result could be processed by EXECUTE
  output                                dcod_valid_o,

  // EXECUTE completed (desired unit is ready)
  output                                exec_valid_o,

  // control WB latches of execution modules
  output                                grant_wb_to_1clk_o,
  output                                grant_wb_to_div_o,
  output                                grant_wb_to_mul_o,
  output                                grant_wb_to_fpxx_arith_o,
  output                                grant_wb_to_lsu_o,
  // for FPU64
  output                                grant_wb_to_fp64_cmp_o,

  // Logic to support Jump / Branch taking
  input                                 dcod_op_jr_i,   // l.jr/l.jalr require operand B (potentially hazard)
  input                                 dcod_op_jimm_i, // l.j/l.jal target selector
  input                                 dcod_op_bf_i,   // l.bf  require awaited flag
  input                                 dcod_op_bnf_i,  // l.bnf require awaited flag
  // pc-relative target
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_to_imm_target_i,
  // register target
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_rfb1_jr_i,
  input      [OPTION_OPERAND_WIDTH-1:0] wb_result1_i,
  // forwarding comparision flag for l.bf/l.bnf
  output reg  [DEST_EXT_ADDR_WIDTH-1:0] dcod_ext_bits_o,
  input                                 busy_op_1clk_cmp_i, // 1-clk flag not computed yet (stall fetch)
  input       [DEST_EXT_ADDR_WIDTH-1:0] busy_ext_bits_1clk_i,
  input                                 exec_wb2exe_hazard_d1xx_i,
  input                                 exec_op_1clk_cmp_i,
  input       [DEST_EXT_ADDR_WIDTH-1:0] exec_ext_bits_1clk_i,
  input                                 exec_flag_set_i, // integer or fp32 comparison result
  input                                 ctrl_flag_i,
  // jump/branch signals to IFETCH
  output                                do_branch_o,
  output     [OPTION_OPERAND_WIDTH-1:0] do_branch_target_o,
  output                                fetch_jr_bc_hazard_o, // jump/branch data not ready
  // Support IBUS error handling in CTRL
  output reg                            wb_jump_or_branch_o,
  output reg                            wb_do_branch_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] wb_do_branch_target_o,


  //   Flag to enabel/disable exterlal interrupts processing
  // depending on the fact is instructions restartable or not
  output                                exec_interrupts_en_o,

  // pre-WB l.rfe
  output                                exec_op_rfe_o,
  // pre-WB output exceptions: IFETCH
  output                                exec_except_ibus_err_o,
  output                                exec_except_ipagefault_o,
  output                                exec_except_itlb_miss_o,
  output                                exec_except_ibus_align_o,
  // pre-WB output exceptions: DECODE
  output                                exec_except_illegal_o,
  output                                exec_except_syscall_o,
  output                                exec_except_trap_o,

  // WB outputs
  //  ## instruction related information
  output reg [OPTION_OPERAND_WIDTH-1:0] pc_wb_o,
  output reg                            wb_delay_slot_o,
  output reg  [DEST_REG_ADDR_WIDTH-1:0] wb_rfd1_adr_o,
  output                                wb_rfd1_wb_o,
  output                                wb_flag_wb_o,
  output reg                            wb_carry_wb_o,
  // for FPU64
  output reg [OPTION_RF_ADDR_WIDTH-1:0] wb_rfd2_adr_o,
  output reg                            wb_rfd2_wb_o
);

  // [O]rder [C]ontrol [B]uffer [T]ap layout
  //  [0...5] Exceptions generated by FETCH & DECODE.
  //    (a) Doesn't include IBUS align violation.
  //        It goes through "jump/branch attributes order control buffer".
  //    (b) LSU exceptions go to WB around any OCB
  //  [6] Flag that external interrupt is enabled (instruction is re-startable)
  localparam  OCBT_INTERRUPTS_EN_POS  = 6;
  //  Unit wise requested/ready
  localparam  OCBT_OP_PASS_EXEC_POS   = OCBT_INTERRUPTS_EN_POS  + 1;
  localparam  OCBT_JUMP_OR_BRANCH_POS = OCBT_OP_PASS_EXEC_POS   + 1;
  localparam  OCBT_OP_1CLK_POS        = OCBT_JUMP_OR_BRANCH_POS + 1;
  localparam  OCBT_OP_DIV_POS         = OCBT_OP_1CLK_POS        + 1;
  localparam  OCBT_OP_MUL_POS         = OCBT_OP_DIV_POS         + 1;
  localparam  OCBT_OP_FPXX_ARITH_POS  = OCBT_OP_MUL_POS         + 1; // arithmetic part only, FP comparison is 1-clock
  localparam  OCBT_OP_FP64_ARITH_POS  = OCBT_OP_FPXX_ARITH_POS  + 1; // it is also source for *_rf_wb2
  localparam  OCBT_OP_FP64_CMP_POS    = OCBT_OP_FP64_ARITH_POS  + 1; // source for granting write back to fp64 comparison
  localparam  OCBT_OP_LS_POS          = OCBT_OP_FP64_CMP_POS    + 1; // load / store (we need it for pushing LSU exceptions)
  localparam  OCBT_OP_RFE_POS         = OCBT_OP_LS_POS          + 1; // l.rfe
  //  Instruction is in delay slot
  localparam  OCBT_DELAY_SLOT_POS     = OCBT_OP_RFE_POS         + 1;
  //  Instruction writting comparison flag
  localparam  OCBT_FLAG_WB_POS        = OCBT_DELAY_SLOT_POS     + 1; // any such instruction
  localparam  OCBT_FLAG_WB_MCYCLE_POS = OCBT_FLAG_WB_POS        + 1; // such istruction is multi-cycle (l.swa, lf.sf*.d)
  //  Instruction writting carry flag
  localparam  OCBT_CARRY_WB_POS       = OCBT_FLAG_WB_MCYCLE_POS + 1;
  //  Instruction generates WB to D1
  localparam  OCBT_RFD1_WB_POS        = OCBT_CARRY_WB_POS       + 1;
  localparam  OCBT_RFD1_ADR_LSB       = OCBT_RFD1_WB_POS        + 1;
  localparam  OCBT_RFD1_ADR_MSB       = OCBT_RFD1_WB_POS        + OPTION_RF_ADDR_WIDTH;
  //  Instruction generates WB to D2
  localparam  OCBT_RFD2_ADR_LSB       = OCBT_RFD1_ADR_MSB       + 1;
  localparam  OCBT_RFD2_ADR_MSB       = OCBT_RFD1_ADR_MSB       + OPTION_RF_ADDR_WIDTH;
  //  Extention to address of RFD, FLAG and CARRY
  localparam  OCBT_EXT_ADR_LSB        = OCBT_RFD2_ADR_MSB       + 1;
  localparam  OCBT_EXT_ADR_MSB        = OCBT_RFD2_ADR_MSB       + DEST_EXT_ADDR_WIDTH;
  //  Program counter
  localparam  OCBT_PC_LSB             = OCBT_EXT_ADR_MSB        + 1;
  localparam  OCBT_PC_MSB             = OCBT_EXT_ADR_MSB        + OPTION_OPERAND_WIDTH;
  //  value of MSB of order control buffer tap
  localparam  OCBT_MSB                = OCBT_PC_MSB;
  localparam  OCBT_WIDTH              = OCBT_MSB                + 1;


  // alias for *_rf_wb2
  localparam  OCBT_RFD2_WB_POS        = OCBT_OP_FP64_ARITH_POS;


  // OMAN WB-request generated with taking into accaunt
  // speculative WB for LSU load command
  //  # WB to RF
  reg wb_rfd1_wb_r;
  //  # WB to FLAG
  reg wb_flag_wb_r;


  // --- initial value for simulations ---
 `ifndef SYNTHESIS // initial value for ext-bits-r
  // synthesis translate_off
  initial dcod_ext_bits_o = {DEST_EXT_ADDR_WIDTH{1'b0}};
  // synthesis translate_on
 `endif // !synth
  // ---
  always @(posedge clk) begin
    if (padv_decode_i)
      dcod_ext_bits_o <= dcod_ext_bits_o + 1'b1;
  end // @clock


  // Flag that istruction is restrartable.
  // Instructions which are not restartable:
  //     "invalid" (empty FETCH result)
  //     "store" - they are buffered and couldn't be removed from buffer
  //               till execution completion
  //     l.msync - it forces LSU to report "busy" till completion of
  //               all previously issued loads and stores
  //     l.mtspr (change internal CPU control registers)
  //     l.rfe (cause return from exception process with serious
  //            changing CPU state).
  //   Note #1 we just not run execution for "invalid" command (CTRL), so
  // such "commands" don't achieve WB where exceptions are processed.
  //   Note #2 l.rfe is a special case. We push pipe full of rfes.
  // The reason for this is that we need the rfe to reach WB stage
  // so it will cause the branch. It will clear itself by the
  // pipeline_flush_i that the rfe will generate.
  wire interrupts_en = ~(dcod_op_lsu_store_i | dcod_op_mtspr_i | dcod_op_msync_i | dcod_op_rfe_i);

  // take branch align exception
  wire dcod_except_ibus_align;

  // Combine DECODE related exceptions
  wire dcod_an_except = dcod_except_ibus_align  |                     // DECODE an exception
                        dcod_except_illegal_i   |                     // DECODE an exception
                        dcod_except_syscall_i   | dcod_except_trap_i; // DECODE an exception

  // input pack
  wire  [OCBT_MSB:0] ocbi;
  assign ocbi = { // various instruction related information
                  pc_decode_i,            // instruction virtual address
                  dcod_ext_bits_o,        // extension to RFD, FLAG or CARRY
                  dcod_rfd2_adr_i,        // WB address D2
                  dcod_rfd1_adr_i,        // WB address D1
                  dcod_rfd1_wb_i,         // instruction generates WB
                  dcod_carry_wb_i,        // istruction affects carry flag
                  dcod_flag_wb_mcycle_i,  // the multy-cycle instruction affects comparison flag
                  dcod_flag_wb_i,         // any instruction which affects comparison flag
                  dcod_delay_slot_i,      // istruction is in delay slot
                  // unit that must be granted for WB
                  dcod_op_rfe_i,     // l.rfe
                  dcod_op_ls_i,      // load / store (we need it for pushing LSU exceptions)
                  dcod_op_fp64_cmp_i,
                  (dcod_op_fpxx_arith_i & dcod_op_fp64_arith_i),
                  dcod_op_fpxx_arith_i,
                  dcod_op_mul_i,
                  dcod_op_div_i,
                  dcod_op_1clk_i,
                  dcod_jump_or_branch_i,
                  (fetch_an_except_i | dcod_an_except | dcod_op_pass_exec_i), // OMAN entrance: !!! l.rfe is in "pass exec" !!!
                  // Flag that istruction is restartable
                  interrupts_en,
                  // FETCH & DECODE exceptions
                  fetch_except_ibus_err_i,
                  fetch_except_ipagefault_i,
                  fetch_except_itlb_miss_i,
                  dcod_except_illegal_i,
                  dcod_except_syscall_i,
                  dcod_except_trap_i };


  wire [OCBT_MSB:0] ocbo00, ocbo01, ocbo02, ocbo03,
                    ocbo04, ocbo05, ocbo06; // 8-th is in Write-Back stage

  wire ocb_full, ocb_empty;


  //-------------------------------//
  // Order Control Buffer instance //
  //-------------------------------//

  mor1kx_ocb_marocchino
  #(
    .NUM_TAPS   (7),          // 8-th is in Write-Back stage
    .NUM_OUTS   (7),          // must be at least 1
    .DATA_SIZE  (OCBT_WIDTH)
  )
  u_ocb
  (
    // clocks, resets and other input controls
    .clk              (clk),
    .rst              (rst),
    .pipeline_flush_i (pipeline_flush_i), // flush pipe
    .padv_decode_i    (padv_decode_i),    // write: advance DECODE
    .padv_wb_i        (padv_wb_i),        // read:  advance WB
    // value at reset/flush
    .default_value_i  ({OCBT_WIDTH{1'b0}}),
    // data input
    .ocbi_i           (ocbi),
    // "OCB is empty" flag
    .empty_o          (ocb_empty),
    // "OCB is full" flag
    //   (a) external control logic must stop the "writing without reading"
    //       operation if OCB is full
    //   (b) however, the "writing + reading" is possible
    //       because it just pushes OCB and keeps it full
    .full_o           (ocb_full),
    // ouput layout
    // { out[n-1], out[n-2], ... out[0] } : DECODE (entrance) -> EXECUTE (exit)
    .ocbo_o           ({ocbo06,ocbo05,ocbo04,ocbo03,ocbo02,ocbo01,ocbo00})
  );


  // Grant WB-access to units
  assign grant_wb_to_1clk_o        = ocbo00[OCBT_OP_1CLK_POS];
  assign grant_wb_to_div_o         = ocbo00[OCBT_OP_DIV_POS];
  assign grant_wb_to_mul_o         = ocbo00[OCBT_OP_MUL_POS];
  assign grant_wb_to_fpxx_arith_o  = ocbo00[OCBT_OP_FPXX_ARITH_POS];
  assign grant_wb_to_lsu_o         = ocbo00[OCBT_OP_LS_POS];
  assign grant_wb_to_fp64_cmp_o    = ocbo00[OCBT_OP_FP64_CMP_POS];


  //--------------------------//
  // Analysis of data hazards //
  //--------------------------//

  // Shorten aliases
  wire [DEST_EXT_ADDR_WIDTH-1:0] wb_rfd1_ext = wb_rfd1_adr_o[(DEST_REG_ADDR_WIDTH-1):OPTION_RF_ADDR_WIDTH];

  // We needn't WB-to-DECODE hazards for FLAG and CARRY:
  //  (a) we process FLAG for l.bf/.bnf in separate way
  //  (b) only 1-clock instructions reqests FLAG/CARRY, so any case they granted with WB accees
  //      after completion FLAG/CARRY update


  // EXEC-to-DECODE hazards by operands
  //  # D1A1
  wire   exe2dec_hazard_d1a1   = (ocbo00[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa1_adr_i) & ocbo00[OCBT_RFD1_WB_POS];
  assign exe2dec_hazard_d1a1_o = exe2dec_hazard_d1a1 & dcod_rfa1_req_i;
  //  # D1B1
  wire   exe2dec_hazard_d1b1   = (ocbo00[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb1_adr_i) & ocbo00[OCBT_RFD1_WB_POS];
  assign exe2dec_hazard_d1b1_o = exe2dec_hazard_d1b1 & dcod_rfb1_req_i;
  //  # D1A2
  wire   exe2dec_hazard_d1a2   = (ocbo00[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa2_adr_i) & ocbo00[OCBT_RFD1_WB_POS];
  assign exe2dec_hazard_d1a2_o = exe2dec_hazard_d1a2 & dcod_rfa2_req_i;
  //  # D1B2
  wire   exe2dec_hazard_d1b2   = (ocbo00[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb2_adr_i) & ocbo00[OCBT_RFD1_WB_POS];
  assign exe2dec_hazard_d1b2_o = exe2dec_hazard_d1b2 & dcod_rfb2_req_i;
  //  # D2A1
  assign exe2dec_hazard_d2a1_o = (ocbo00[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa1_adr_i) & ocbo00[OCBT_RFD2_WB_POS] & dcod_rfa1_req_i;
  //  # D2B1
  assign exe2dec_hazard_d2b1_o = (ocbo00[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb1_adr_i) & ocbo00[OCBT_RFD2_WB_POS] & dcod_rfb1_req_i;
  //  # D2A2
  assign exe2dec_hazard_d2a2_o = (ocbo00[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa2_adr_i) & ocbo00[OCBT_RFD2_WB_POS] & dcod_rfa2_req_i;
  //  # D2B2
  assign exe2dec_hazard_d2b2_o = (ocbo00[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb2_adr_i) & ocbo00[OCBT_RFD2_WB_POS] & dcod_rfb2_req_i;


  // EXEC-to-DECODE combined flags to control reservation stations
  // --- for all RSRVS ---
  wire   exe2dec_a_hazard_common = exe2dec_hazard_d2b1_o | exe2dec_hazard_d2a1_o | // EXEC-to-DECODE combined flag for all RSRVS
                                   exe2dec_hazard_d1b1_o | exe2dec_hazard_d1a1_o;  // EXEC-to-DECODE combined flag for all RSRVS
  // --- for RSRVS-LSU ---
  assign exe2dec_a_hazard_lsu_o  = exe2dec_a_hazard_common;
  // --- for RSRVS-1CLK ---
  assign exe2dec_a_hazard_1clk_o = exe2dec_a_hazard_common;
  // --- for RSRVS-MCLK ---
  assign exe2dec_a_hazard_mclk_o = exe2dec_hazard_d2b2_o | exe2dec_hazard_d2a2_o | // EXEC-to-DECODE combined flag for RSRVS-MCLK
                                   exe2dec_hazard_d1b2_o | exe2dec_hazard_d1a2_o | // EXEC-to-DECODE combined flag for RSRVS-MCLK
                                   exe2dec_a_hazard_common;                        // EXEC-to-DECODE combined flag for RSRVS-MCLK


  // OMAN-to-DECODE hazards by operands

  // D1A1
  // OMAN-to-DECODE hazards D1A1
  wire ocbo06_hazard_d1a1 = (ocbo06[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa1_adr_i) & ocbo06[OCBT_RFD1_WB_POS];
  wire ocbo05_hazard_d1a1 = (ocbo05[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa1_adr_i) & ocbo05[OCBT_RFD1_WB_POS];
  wire ocbo04_hazard_d1a1 = (ocbo04[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa1_adr_i) & ocbo04[OCBT_RFD1_WB_POS];
  wire ocbo03_hazard_d1a1 = (ocbo03[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa1_adr_i) & ocbo03[OCBT_RFD1_WB_POS];
  wire ocbo02_hazard_d1a1 = (ocbo02[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa1_adr_i) & ocbo02[OCBT_RFD1_WB_POS];
  wire ocbo01_hazard_d1a1 = (ocbo01[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa1_adr_i) & ocbo01[OCBT_RFD1_WB_POS];
  // OMAN-to-DECODE hazard D1A1: combined flag
  wire omn2dec_hazard_d1a1 = (ocbo06_hazard_d1a1 | ocbo05_hazard_d1a1 | ocbo04_hazard_d1a1 |
                              ocbo03_hazard_d1a1 | ocbo02_hazard_d1a1 | ocbo01_hazard_d1a1 |
                              (dcod_wb2dec_eq_adr_d1a1_i & wb_rfd1_wb_r & wb_rfd1_wb_lsu_miss_i)) & dcod_rfa1_req_i;
  // Reservation station busy D1A1: hazard flag
  assign busy_hazard_d1a1_o = omn2dec_hazard_d1a1 | exe2dec_hazard_d1a1_o;
  // Reservation station busy D1A1: ext-bits
  assign busy_hazard_d1a1_adr_o = ocbo06_hazard_d1a1  ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo05_hazard_d1a1  ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo04_hazard_d1a1  ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo03_hazard_d1a1  ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo02_hazard_d1a1  ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo01_hazard_d1a1  ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  exe2dec_hazard_d1a1 ? ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                        wb_rfd1_ext;


  // D1B1
  // OMAN-to-DECODE hazards D1B1
  wire ocbo06_hazard_d1b1 = (ocbo06[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb1_adr_i) & ocbo06[OCBT_RFD1_WB_POS];
  wire ocbo05_hazard_d1b1 = (ocbo05[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb1_adr_i) & ocbo05[OCBT_RFD1_WB_POS];
  wire ocbo04_hazard_d1b1 = (ocbo04[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb1_adr_i) & ocbo04[OCBT_RFD1_WB_POS];
  wire ocbo03_hazard_d1b1 = (ocbo03[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb1_adr_i) & ocbo03[OCBT_RFD1_WB_POS];
  wire ocbo02_hazard_d1b1 = (ocbo02[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb1_adr_i) & ocbo02[OCBT_RFD1_WB_POS];
  wire ocbo01_hazard_d1b1 = (ocbo01[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb1_adr_i) & ocbo01[OCBT_RFD1_WB_POS];
  // OMAN-to-DECODE hazard D1B1: combined flag
  wire omn2dec_hazard_d1b1 = (ocbo06_hazard_d1b1 | ocbo05_hazard_d1b1 | ocbo04_hazard_d1b1 |
                              ocbo03_hazard_d1b1 | ocbo02_hazard_d1b1 | ocbo01_hazard_d1b1 |
                              (dcod_wb2dec_eq_adr_d1b1_i & wb_rfd1_wb_r & wb_rfd1_wb_lsu_miss_i)) & dcod_rfb1_req_i;
  // Reservation station busy D1B1: hazard flag
  assign busy_hazard_d1b1_o = omn2dec_hazard_d1b1 | exe2dec_hazard_d1b1_o;
  // Reservation station busy D1B1: ext-bits
  assign busy_hazard_d1b1_adr_o = ocbo06_hazard_d1b1  ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo05_hazard_d1b1  ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo04_hazard_d1b1  ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo03_hazard_d1b1  ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo02_hazard_d1b1  ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo01_hazard_d1b1  ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  exe2dec_hazard_d1b1 ? ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                        wb_rfd1_ext;


  // D1A2
  // OMAN-to-DECODE hazards D1A2
  wire ocbo06_hazard_d1a2 = (ocbo06[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa2_adr_i) & ocbo06[OCBT_RFD1_WB_POS];
  wire ocbo05_hazard_d1a2 = (ocbo05[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa2_adr_i) & ocbo05[OCBT_RFD1_WB_POS];
  wire ocbo04_hazard_d1a2 = (ocbo04[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa2_adr_i) & ocbo04[OCBT_RFD1_WB_POS];
  wire ocbo03_hazard_d1a2 = (ocbo03[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa2_adr_i) & ocbo03[OCBT_RFD1_WB_POS];
  wire ocbo02_hazard_d1a2 = (ocbo02[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa2_adr_i) & ocbo02[OCBT_RFD1_WB_POS];
  wire ocbo01_hazard_d1a2 = (ocbo01[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa2_adr_i) & ocbo01[OCBT_RFD1_WB_POS];
  // OMAN-to-DECODE hazard D1A2: combined flag
  wire omn2dec_hazard_d1a2 = (ocbo06_hazard_d1a2 | ocbo05_hazard_d1a2 | ocbo04_hazard_d1a2 |
                              ocbo03_hazard_d1a2 | ocbo02_hazard_d1a2 | ocbo01_hazard_d1a2 |
                              (dcod_wb2dec_eq_adr_d1a2_i & wb_rfd1_wb_r & wb_rfd1_wb_lsu_miss_i)) & dcod_rfa2_req_i;
  // Reservation station busy D1A2: hazard flag
  assign busy_hazard_d1a2_o = omn2dec_hazard_d1a2 | exe2dec_hazard_d1a2_o;
  // Reservation station busy D1A2: ext-bits
  assign busy_hazard_d1a2_adr_o = ocbo06_hazard_d1a2  ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo05_hazard_d1a2  ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo04_hazard_d1a2  ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo03_hazard_d1a2  ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo02_hazard_d1a2  ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo01_hazard_d1a2  ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  exe2dec_hazard_d1a2 ? ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                        wb_rfd1_ext;


  // D1B2
  // OMAN-to-DECODE hazards D1B2
  wire ocbo06_hazard_d1b2 = (ocbo06[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb2_adr_i) & ocbo06[OCBT_RFD1_WB_POS];
  wire ocbo05_hazard_d1b2 = (ocbo05[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb2_adr_i) & ocbo05[OCBT_RFD1_WB_POS];
  wire ocbo04_hazard_d1b2 = (ocbo04[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb2_adr_i) & ocbo04[OCBT_RFD1_WB_POS];
  wire ocbo03_hazard_d1b2 = (ocbo03[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb2_adr_i) & ocbo03[OCBT_RFD1_WB_POS];
  wire ocbo02_hazard_d1b2 = (ocbo02[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb2_adr_i) & ocbo02[OCBT_RFD1_WB_POS];
  wire ocbo01_hazard_d1b2 = (ocbo01[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb2_adr_i) & ocbo01[OCBT_RFD1_WB_POS];
  // OMAN-to-DECODE hazard D1B2: combined flag
  wire omn2dec_hazard_d1b2 = (ocbo06_hazard_d1b2 | ocbo05_hazard_d1b2 | ocbo04_hazard_d1b2 |
                              ocbo03_hazard_d1b2 | ocbo02_hazard_d1b2 | ocbo01_hazard_d1b2 |
                              (dcod_wb2dec_eq_adr_d1b2_i & wb_rfd1_wb_r & wb_rfd1_wb_lsu_miss_i)) & dcod_rfb2_req_i;
  // Reservation station busy D1B2: hazard flag
  assign busy_hazard_d1b2_o = omn2dec_hazard_d1b2 | exe2dec_hazard_d1b2_o;
  // Reservation station busy D1B2: ext-bits
  assign busy_hazard_d1b2_adr_o = ocbo06_hazard_d1b2  ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo05_hazard_d1b2  ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo04_hazard_d1b2  ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo03_hazard_d1b2  ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo02_hazard_d1b2  ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo01_hazard_d1b2  ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  exe2dec_hazard_d1b2 ? ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                        wb_rfd1_ext;


  // D2A1
  wire ocbo06_hazard_d2a1 = (ocbo06[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa1_adr_i) & ocbo06[OCBT_RFD2_WB_POS];
  wire ocbo05_hazard_d2a1 = (ocbo05[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa1_adr_i) & ocbo05[OCBT_RFD2_WB_POS];
  wire ocbo04_hazard_d2a1 = (ocbo04[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa1_adr_i) & ocbo04[OCBT_RFD2_WB_POS];
  wire ocbo03_hazard_d2a1 = (ocbo03[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa1_adr_i) & ocbo03[OCBT_RFD2_WB_POS];
  wire ocbo02_hazard_d2a1 = (ocbo02[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa1_adr_i) & ocbo02[OCBT_RFD2_WB_POS];
  wire ocbo01_hazard_d2a1 = (ocbo01[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa1_adr_i) & ocbo01[OCBT_RFD2_WB_POS];
  // OMAN-to-DECODE hazard D2A1
  wire omn2dec_hazard_d2a1 = (ocbo06_hazard_d2a1 | ocbo05_hazard_d2a1 |
                              ocbo04_hazard_d2a1 | ocbo03_hazard_d2a1 |
                              ocbo02_hazard_d2a1 | ocbo01_hazard_d2a1) & dcod_rfa1_req_i;
  // Reservation station busy D2A1: hazard flag
  assign busy_hazard_d2a1_o = omn2dec_hazard_d2a1 | exe2dec_hazard_d2a1_o;
  // Reservation station busy D2A1: ext-bits
  assign busy_hazard_d2a1_adr_o = ocbo06_hazard_d2a1 ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo05_hazard_d2a1 ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo04_hazard_d2a1 ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo03_hazard_d2a1 ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo02_hazard_d2a1 ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo01_hazard_d2a1 ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                       ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB];


  // D2B1
  wire ocbo06_hazard_d2b1 = (ocbo06[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb1_adr_i) & ocbo06[OCBT_RFD2_WB_POS];
  wire ocbo05_hazard_d2b1 = (ocbo05[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb1_adr_i) & ocbo05[OCBT_RFD2_WB_POS];
  wire ocbo04_hazard_d2b1 = (ocbo04[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb1_adr_i) & ocbo04[OCBT_RFD2_WB_POS];
  wire ocbo03_hazard_d2b1 = (ocbo03[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb1_adr_i) & ocbo03[OCBT_RFD2_WB_POS];
  wire ocbo02_hazard_d2b1 = (ocbo02[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb1_adr_i) & ocbo02[OCBT_RFD2_WB_POS];
  wire ocbo01_hazard_d2b1 = (ocbo01[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb1_adr_i) & ocbo01[OCBT_RFD2_WB_POS];
  // OMAN-to-DECODE hazard D2B1
  wire omn2dec_hazard_d2b1 = (ocbo06_hazard_d2b1 | ocbo05_hazard_d2b1 |
                              ocbo04_hazard_d2b1 | ocbo03_hazard_d2b1 |
                              ocbo02_hazard_d2b1 | ocbo01_hazard_d2b1) & dcod_rfb1_req_i;
  // Reservation station busy D2B1: hazard flag
  assign busy_hazard_d2b1_o = omn2dec_hazard_d2b1 | exe2dec_hazard_d2b1_o;
  // Reservation station busy D2B1: ext-bits
  assign busy_hazard_d2b1_adr_o = ocbo06_hazard_d2b1 ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo05_hazard_d2b1 ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo04_hazard_d2b1 ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo03_hazard_d2b1 ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo02_hazard_d2b1 ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo01_hazard_d2b1 ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                       ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB];


  // D2A2
  wire ocbo06_hazard_d2a2 = (ocbo06[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa2_adr_i) & ocbo06[OCBT_RFD2_WB_POS];
  wire ocbo05_hazard_d2a2 = (ocbo05[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa2_adr_i) & ocbo05[OCBT_RFD2_WB_POS];
  wire ocbo04_hazard_d2a2 = (ocbo04[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa2_adr_i) & ocbo04[OCBT_RFD2_WB_POS];
  wire ocbo03_hazard_d2a2 = (ocbo03[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa2_adr_i) & ocbo03[OCBT_RFD2_WB_POS];
  wire ocbo02_hazard_d2a2 = (ocbo02[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa2_adr_i) & ocbo02[OCBT_RFD2_WB_POS];
  wire ocbo01_hazard_d2a2 = (ocbo01[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa2_adr_i) & ocbo01[OCBT_RFD2_WB_POS];
  // OMAN-to-DECODE hazard D2A2
  wire omn2dec_hazard_d2a2 = (ocbo06_hazard_d2a2 | ocbo05_hazard_d2a2 |
                              ocbo04_hazard_d2a2 | ocbo03_hazard_d2a2 |
                              ocbo02_hazard_d2a2 | ocbo01_hazard_d2a2) & dcod_rfa2_req_i;
  // Reservation station busy D2A2: hazard flag
  assign busy_hazard_d2a2_o = omn2dec_hazard_d2a2 | exe2dec_hazard_d2a2_o;
  // Reservation station busy D2A2: ext-bits
  assign busy_hazard_d2a2_adr_o = ocbo06_hazard_d2a2 ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo05_hazard_d2a2 ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo04_hazard_d2a2 ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo03_hazard_d2a2 ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo02_hazard_d2a2 ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo01_hazard_d2a2 ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                       ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB];


  // D2B2
  wire ocbo06_hazard_d2b2 = (ocbo06[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb2_adr_i) & ocbo06[OCBT_RFD2_WB_POS];
  wire ocbo05_hazard_d2b2 = (ocbo05[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb2_adr_i) & ocbo05[OCBT_RFD2_WB_POS];
  wire ocbo04_hazard_d2b2 = (ocbo04[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb2_adr_i) & ocbo04[OCBT_RFD2_WB_POS];
  wire ocbo03_hazard_d2b2 = (ocbo03[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb2_adr_i) & ocbo03[OCBT_RFD2_WB_POS];
  wire ocbo02_hazard_d2b2 = (ocbo02[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb2_adr_i) & ocbo02[OCBT_RFD2_WB_POS];
  wire ocbo01_hazard_d2b2 = (ocbo01[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb2_adr_i) & ocbo01[OCBT_RFD2_WB_POS];
  // OMAN-to-DECODE hazard D2B2
  wire omn2dec_hazard_d2b2 = (ocbo06_hazard_d2b2 | ocbo05_hazard_d2b2 |
                              ocbo04_hazard_d2b2 | ocbo03_hazard_d2b2 |
                              ocbo02_hazard_d2b2 | ocbo01_hazard_d2b2) & dcod_rfb2_req_i;
  // Reservation station busy D2B2: hazard flag
  assign busy_hazard_d2b2_o = omn2dec_hazard_d2b2 | exe2dec_hazard_d2b2_o;
  // Reservation station busy D2B2: ext-bits
  assign busy_hazard_d2b2_adr_o = ocbo06_hazard_d2b2 ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo05_hazard_d2b2 ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo04_hazard_d2b2 ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo03_hazard_d2b2 ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo02_hazard_d2b2 ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                  ocbo01_hazard_d2b2 ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                       ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB];


  // OMAN-to-DECODE combined flags
  wire   omn2dec_a_hazard_common = omn2dec_hazard_d2b1 | omn2dec_hazard_d2a1 | // OMAN-to-DECODE for all RSRVS
                                   omn2dec_hazard_d1b1 | omn2dec_hazard_d1a1;  // OMAN-to-DECODE for all RSRVS
  // --- for RSRVS-LSU ---
  assign omn2dec_a_hazard_lsu_o  = omn2dec_a_hazard_common;
  // --- for RSRVS-1CLK ---
  assign omn2dec_a_hazard_1clk_o = omn2dec_a_hazard_common;
  // --- for RSRVS-MCLK ---
  assign omn2dec_a_hazard_mclk_o = omn2dec_hazard_d2b2 | omn2dec_hazard_d2a2 | // OMAN-to-DECODE for all RSRVS-MCLK
                                   omn2dec_hazard_d1b2 | omn2dec_hazard_d1a2 | // OMAN-to-DECODE for all RSRVS-MCLK
                                   omn2dec_a_hazard_common;                    // OMAN-to-DECODE for all RSRVS-MCLK




  // Data for resolving hazards by passing from DECODE to EXECUTE
  assign exec_rfd1_wb_o  = ocbo00[OCBT_RFD1_WB_POS];
  assign exec_rfd2_wb_o  = ocbo00[OCBT_RFD2_WB_POS];
  assign exec_ext_adr_o  = ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB];


  //   An execute module is ready and granted access to WB
  //   Instructions l.mf(t)spr have got guaranted WB access because
  // no any new instruction is issued into execution till
  // l.mf(t)spr has been completed. Pay attention that we start
  // l.mf(t)spr ecxecution after completion of all peviously
  // issued instructions only.
  //   l.rfe and FETCH/DECODE exceptions are also should
  // push WB latches
  // ---
  //   Declaration valid flag for jump/branch attributes
  wire   exec_jb_attr_valid;
  // ---
  //   For l.jal/l.jalr we use adder in 1-clk to compure return address,
  // so for the cases we additionally wait "jump/branch attributes".
  assign exec_valid_o =
    (exec_op_1clk_i     & ocbo00[OCBT_OP_1CLK_POS] & ~ocbo00[OCBT_JUMP_OR_BRANCH_POS]) | // EXEC VALID: but wait attributes for l.jal/ljalr
    (div_valid_i        & ocbo00[OCBT_OP_DIV_POS])         | // EXEC VALID
    (mul_valid_i        & ocbo00[OCBT_OP_MUL_POS])         | // EXEC VALID
    (fpxx_arith_valid_i & ocbo00[OCBT_OP_FPXX_ARITH_POS])  | // EXEC VALID
    (exec_op_fp64_cmp_i & ocbo00[OCBT_OP_FP64_CMP_POS])    | // EXEC VALID
    (lsu_valid_i        & ocbo00[OCBT_OP_LS_POS])          | // EXEC VALID
    (exec_jb_attr_valid & ocbo00[OCBT_JUMP_OR_BRANCH_POS]) | // EXEC VALID
                          ocbo00[OCBT_OP_PASS_EXEC_POS];     // EXEC VALID: l.rfe and FETCH/DECODE exceptions, etc

  // DECODE stall components
  //  stall by unit usage hazard
  //     (unit could be either busy or waiting for WB access)
  wire stall_by_hazard_u =
    (dcod_op_1clk_i & op_1clk_busy_i) |
    ((dcod_op_mul_i | dcod_op_div_i | dcod_op_fpxx_arith_i | dcod_op_fp64_cmp_i) & mclk_busy_i) |
    ((dcod_op_ls_i | dcod_op_msync_i) & lsu_busy_i);

  //  stall by:
  //    a) MF(T)SPR in decode till and OCB become empty (see here)
  //    b) till completion MF(T)SPR (see CTRL)
  //       this completion generates padv-wb,
  //       in next turn padv-wb cleans up OCB and restores
  //       instructions issue
  wire stall_by_mXspr = (dcod_op_mtspr_i | dcod_op_mfspr_i) & ((~ocb_empty) | wb_lsu_valid_miss_i);

  // combine stalls to decode-valid flag
  assign dcod_valid_o = (~stall_by_hazard_u) & (~ocb_full) & (~stall_by_mXspr);


  //---------------------------------------//
  // Logic to support Jump / Branch taking //
  //---------------------------------------//

  // Take branch pendings related to l.jr/l.jalr
  reg                           op_jr_p;
  reg [DEST_EXT_ADDR_WIDTH-1:0] op_jr_d1b1_adr_p;
  // --- combined D1B1 potential hazards related l.jr/l.jalr ---
  wire ocb_hazard_d1b1 = ocbo06_hazard_d1b1 | ocbo05_hazard_d1b1 |
                         ocbo04_hazard_d1b1 | ocbo03_hazard_d1b1 |
                         ocbo02_hazard_d1b1 | ocbo01_hazard_d1b1 |
                         exe2dec_hazard_d1b1;
  // ---
  wire dcod_jr_hazard = ocb_hazard_d1b1 |                                                   // l.jr/l.jalr hazard in DECODE
                        (dcod_wb2dec_eq_adr_d1b1_i & wb_rfd1_wb_r & wb_rfd1_wb_lsu_miss_i); // l.jr/l.jalr hazard in DECODE
  // ---
  wire oman_jr_hazard = (op_jr_d1b1_adr_p != wb_rfd1_ext) | (wb_rfd1_wb_r & wb_rfd1_wb_lsu_miss_i); // l.jr/l.jalr hazard in OMAN
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      op_jr_p <= 1'b0;
    else if (pipeline_flush_i)
      op_jr_p <= 1'b0;
    else if (op_jr_p)
      op_jr_p <= oman_jr_hazard;
    else if (padv_decode_i) begin
      op_jr_p          <= dcod_op_jr_i & dcod_jr_hazard;
      op_jr_d1b1_adr_p <= busy_hazard_d1b1_adr_o;
    end
  end // @clock


  // Take branch pendings related to l.bf/l.bnf
  reg                            op_bf_p, op_bnf_p, op_bc_p;
  reg [OPTION_OPERAND_WIDTH-1:0] dcod_to_imm_target_p;
  wire [DEST_EXT_ADDR_WIDTH-1:0] op_bc_flag_adr;
  reg  [DEST_EXT_ADDR_WIDTH-1:0] op_bc_flag_adr_p;
  // ---
  wire dcod_op_bc = dcod_op_bf_i | dcod_op_bnf_i;
  // ---
  assign op_bc_flag_adr = ocbo06[OCBT_FLAG_WB_POS] ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                          ocbo05[OCBT_FLAG_WB_POS] ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                          ocbo04[OCBT_FLAG_WB_POS] ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                          ocbo03[OCBT_FLAG_WB_POS] ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                          ocbo02[OCBT_FLAG_WB_POS] ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                          ocbo01[OCBT_FLAG_WB_POS] ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                          ocbo00[OCBT_FLAG_WB_POS] ? ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                     wb_rfd1_ext;
  // --- waiting computation of multi-cycle flag (l.bf/l.bnf related) ---
  wire ocb_flag_mcycle = ocbo06[OCBT_FLAG_WB_MCYCLE_POS] | ocbo05[OCBT_FLAG_WB_MCYCLE_POS] |
                         ocbo04[OCBT_FLAG_WB_MCYCLE_POS] | ocbo03[OCBT_FLAG_WB_MCYCLE_POS] |
                         ocbo02[OCBT_FLAG_WB_MCYCLE_POS] | ocbo01[OCBT_FLAG_WB_MCYCLE_POS] |
                         ocbo00[OCBT_FLAG_WB_MCYCLE_POS];
  reg  ocb_flag_mcycle_p; // pending
  // ---
  wire dcod_bc_hazard = busy_op_1clk_cmp_i |                                                  // l.bf/l.bnf hazard in DECODE
                        (exec_op_1clk_cmp_i & exec_wb2exe_hazard_d1xx_i & (~wb_rfd1_wb_o)) |  // l.bf/l.bnf hazard in DECODE
                        ocb_flag_mcycle | (wb_flag_wb_r & wb_flag_wb_lsu_miss_i);             // l.bf/l.bnf hazard in DECODE
  reg  op_1clk_cmp_p;
  // ---
  wire oman_bc_hazard = (op_1clk_cmp_p & ((busy_op_1clk_cmp_i & (op_bc_flag_adr_p == busy_ext_bits_1clk_i)) |     // l.bf/l.bnf hazard in OMAN
                                          (op_bc_flag_adr_p != exec_ext_bits_1clk_i) |                            // l.bf/l.bnf hazard in OMAN
                                          (exec_op_1clk_cmp_i & exec_wb2exe_hazard_d1xx_i & (~wb_rfd1_wb_o)))) |  // l.bf/l.bnf hazard in OMAN
                        (ocb_flag_mcycle_p & ((op_bc_flag_adr_p != wb_rfd1_ext) |                                 // l.bf/l.bnf hazard in OMAN
                                              (wb_flag_wb_r & wb_flag_wb_lsu_miss_i)));                           // l.bf/l.bnf hazard in OMAN
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      op_bf_p           <= 1'b0;
      op_bnf_p          <= 1'b0;
      op_bc_p           <= 1'b0;
      ocb_flag_mcycle_p <= 1'b0;
      op_1clk_cmp_p     <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      op_bf_p           <= 1'b0;
      op_bnf_p          <= 1'b0;
      op_bc_p           <= 1'b0;
      ocb_flag_mcycle_p <= 1'b0;
      op_1clk_cmp_p     <= 1'b0;
    end
    else if (op_bc_p) begin
      op_bf_p           <= oman_bc_hazard & op_bf_p;
      op_bnf_p          <= oman_bc_hazard & op_bnf_p;
      op_bc_p           <= oman_bc_hazard;
      ocb_flag_mcycle_p <= oman_bc_hazard & ocb_flag_mcycle_p;
      op_1clk_cmp_p     <= oman_bc_hazard & op_1clk_cmp_p;
    end
    else if (padv_decode_i) begin
      op_bf_p              <= dcod_op_bf_i  & dcod_bc_hazard;
      op_bnf_p             <= dcod_op_bnf_i & dcod_bc_hazard;
      op_bc_p              <= dcod_op_bc    & dcod_bc_hazard;
      ocb_flag_mcycle_p    <= ocb_flag_mcycle;
      op_1clk_cmp_p        <= ~ocb_flag_mcycle;
      dcod_to_imm_target_p <= dcod_to_imm_target_i;
      op_bc_flag_adr_p     <= op_bc_flag_adr;
    end
  end // @clock


  // Combine IFETCH hazards
  assign fetch_jr_bc_hazard_o = (dcod_op_jr_i & dcod_jr_hazard) | (op_jr_p & oman_jr_hazard) | // IFETCH waiting rB for l.jr/l.jalr
                                (dcod_op_bc   & dcod_bc_hazard) | (op_bc_p & oman_bc_hazard);  // IFETCH waiting flag for l.bf/l.bnf
  // forwarded flag
  wire fwd_flag = exec_op_1clk_cmp_i ? exec_flag_set_i : ctrl_flag_i;
  // ---
  assign do_branch_o = dcod_op_jr_i    | op_jr_p |                // do jump to register (B1)
                       dcod_op_jimm_i  |                          // do jump to immediate
                       ((dcod_op_bf_i  | op_bf_p)  &  fwd_flag) | // do branch by flag
                       ((dcod_op_bnf_i | op_bnf_p) & ~fwd_flag);  // do branch by ~flag
  // branch target
  assign do_branch_target_o = op_jr_p      ? wb_result1_i         : // branch target selection
                              op_bc_p      ? dcod_to_imm_target_p : // branch target selection
                              dcod_op_jr_i ? dcod_rfb1_jr_i       : // branch target selection
                                             dcod_to_imm_target_i;  // branch target selection


  // Detect IBUS align violation on DECODE stage.
  // To compute "oman_fd_an_except_o" and for JB_ATTR_OCB
  // It could happen only for l.jr/l.jalr
  assign dcod_except_ibus_align = dcod_op_jr_i & (~dcod_jr_hazard) & (|dcod_rfb1_jr_i[1:0]);

  // Detect IBUS align violation on OMAN.
  // For JB_ATTR_OCB only.
  wire   oman_except_ibus_align = op_jr_p & (~oman_jr_hazard) & (|wb_result1_i[1:0]);


  // JUMP/BRANCH attributes [O]rder [C]ontrol [B]uffer (JB_ATTR_OCB)
  localparam  JB_ATTR_TARGET_LSB            = 0;
  localparam  JB_ATTR_TARGET_MSB            = OPTION_OPERAND_WIDTH          - 1;
  localparam  JB_ATTR_DO_BRANCH_POS         = JB_ATTR_TARGET_MSB            + 1; // if "do" the "target" makes sence
  localparam  JP_ATTR_EXCEPT_IBUS_ALIGN_POS = JB_ATTR_DO_BRANCH_POS         + 1;
  localparam  JB_ATTR_VALID_POS             = JP_ATTR_EXCEPT_IBUS_ALIGN_POS + 1;
  //---
  localparam  JB_ATTR_MSB   = JB_ATTR_VALID_POS;
  localparam  JB_ATTR_WIDTH = JB_ATTR_MSB + 1;
  // --- input data fields for JB_ATTR_OCB ---
  wire [JB_ATTR_MSB:0] jb_attr_ocbi =
    {
      1'b1,                                              // JB_ATTR_OCB input fields: if pushed into JB_ATTR_OCB then valid
      (dcod_except_ibus_align | oman_except_ibus_align), // JB_ATTR_OCB input fields: align exception
      do_branch_o,                                       // JB_ATTR_OCB input fields: jump or taken branch
      do_branch_target_o                                 // JB_ATTR_OCB input fields
    };
  // --- output data fields for JB_ATTR_OCB ---
  wire [JB_ATTR_MSB:0] jb_attr_ocbo;
  // --- push new data to JB_ATTR_OCB ---
  wire push_jb_attr_ocb = (padv_decode_i & ( dcod_op_jimm_i                  |    // PUSH JB_ATTR_OCB from DECODE
                                            (dcod_op_jr_i & ~dcod_jr_hazard) |    // PUSH JB_ATTR_OCB from DECODE
                                            (dcod_op_bc   & ~dcod_bc_hazard))) |  // PUSH JB_ATTR_OCB from DECODE
                          (op_jr_p & ~oman_jr_hazard) |                           // PUSH JB_ATTR_OCB from OMAN
                          (op_bc_p & ~oman_bc_hazard);                            // PUSH JB_ATTR_OCB from OMAN
  // --- "read" buffer output ---
  wire read_jb_attr_ocb = padv_wb_i & ocbo00[OCBT_JUMP_OR_BRANCH_POS];
  // --- JB_ATTR_OCB instance ---
  mor1kx_ocb_marocchino
  #(
    .NUM_TAPS   (4), // half of regular OCB (second half is delay slots)
    .NUM_OUTS   (1), // only "EXECUTE" level is intresting
    .DATA_SIZE  (JB_ATTR_WIDTH)
  )
  u_jb_attr_ocb
  (
    // clocks and resets
    .clk                (clk), // JB_ATTR_OCB
    .rst                (rst), // JB_ATTR_OCB
    // pipe controls
    .pipeline_flush_i   (pipeline_flush_i), // JB_ATTR_OCB
    .padv_decode_i      (push_jb_attr_ocb), // JB_ATTR_OCB
    .padv_wb_i          (read_jb_attr_ocb), // JB_ATTR_OCB
    // value at reset/flush
    .default_value_i    ({JB_ATTR_WIDTH{1'b0}}), // JB_ATTR_OCB
    // data input
    .ocbi_i             (jb_attr_ocbi), // JB_ATTR_OCB
    // "OCB is empty" flag
    .empty_o            (), // JB_ATTR_OCB
    // "OCB is full" flag
    .full_o             (), // JB_ATTR_OCB
    // data ouputs
    .ocbo_o             (jb_attr_ocbo) // JB_ATTR_OCB
  );
  // --- JB_ATTR_OCB output unpack ---
  assign exec_jb_attr_valid = jb_attr_ocbo[JB_ATTR_VALID_POS];

  // WB JUMP or BRANCH attributes
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      wb_jump_or_branch_o <= 1'b0;
      wb_do_branch_o      <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      wb_jump_or_branch_o <= 1'b0;
      wb_do_branch_o      <= 1'b0;
    end
    else if (padv_wb_i) begin
      wb_jump_or_branch_o   <= ocbo00[OCBT_JUMP_OR_BRANCH_POS];
      wb_do_branch_o        <= jb_attr_ocbo[JB_ATTR_DO_BRANCH_POS];
      wb_do_branch_target_o <= jb_attr_ocbo[JB_ATTR_TARGET_MSB:JB_ATTR_TARGET_LSB];
    end
    else begin
      wb_jump_or_branch_o <= 1'b0; // 1-clock length
      wb_do_branch_o      <= 1'b0;
    end
  end // @clock


  // ---
  // Stall DECODE advancing (see also CTRL) when l.rfe or ecxeptions are in EXECUTE stage.
  // The main purpose of this is waiting till l.rfe/exceptions propagate up to WB stage.
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      oman_fd_an_except_o <= 1'b0;
    else if (pipeline_flush_i)
      oman_fd_an_except_o <= 1'b0;
    else if (padv_decode_i)
      oman_fd_an_except_o <= (fetch_an_except_i | dcod_an_except  | dcod_op_rfe_i);
  end

  //   Flag to enabel/disable exterlal interrupts processing
  // depending on the fact is instructions restartable or not
  assign exec_interrupts_en_o     = ocbo00[OCBT_INTERRUPTS_EN_POS];

  // pre-WB l.rfe
  assign exec_op_rfe_o            = ocbo00[OCBT_OP_RFE_POS];
  // IFETCH exceptions
  assign exec_except_ibus_err_o   = ocbo00[5];
  assign exec_except_ipagefault_o = ocbo00[4];
  assign exec_except_itlb_miss_o  = ocbo00[3];
  assign exec_except_ibus_align_o = jb_attr_ocbo[JP_ATTR_EXCEPT_IBUS_ALIGN_POS];
  // DECODE exceptions
  assign exec_except_illegal_o    = ocbo00[2];
  assign exec_except_syscall_o    = ocbo00[1];
  assign exec_except_trap_o       = ocbo00[0];

  // PC at EXECUTE (moslty for debugging)
  wire [OPTION_OPERAND_WIDTH-1:0] pc_exec = ocbo00[OCBT_PC_MSB:OCBT_PC_LSB];



  // D1 WB-to-RF request generated with taking
  // into accaunt speculative WB for LSU load command
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_rfd1_wb_r <= 1'b0;
    else if (pipeline_flush_i)
      wb_rfd1_wb_r <= 1'b0;
    else if (padv_wb_i)
      wb_rfd1_wb_r <= ocbo00[OCBT_RFD1_WB_POS];
    else if (~wb_rfd1_wb_lsu_miss_i)
      wb_rfd1_wb_r <= 1'b0;
  end // @clock
  // ---
  assign wb_rfd1_wb_o = wb_rfd1_wb_r & (~wb_rfd1_wb_lsu_miss_i);


  // D2 WB-to-RF request (1-clock length)
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_rfd2_wb_o <= 1'b0;
    else if (pipeline_flush_i)
      wb_rfd2_wb_o <= 1'b0;
    else if (padv_wb_i)
      wb_rfd2_wb_o <= ocbo00[OCBT_RFD2_WB_POS];
    else
      wb_rfd2_wb_o <= 1'b0;
  end // @clock


  // OMAN WB-to-FLAG-request generated with taking
  // into accaunt speculative WB for LSU load command
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_flag_wb_r <= 1'b0;
    else if (pipeline_flush_i)
      wb_flag_wb_r <= 1'b0;
    else if (padv_wb_i)
      wb_flag_wb_r <= ocbo00[OCBT_FLAG_WB_POS];
    else if (~wb_flag_wb_lsu_miss_i)
      wb_flag_wb_r <= 1'b0;
  end // @clock
  // ---
  assign wb_flag_wb_o = wb_flag_wb_r & (~wb_flag_wb_lsu_miss_i);


  // WB-to-CARRY-request (1-clock to prevent extra writes)
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_carry_wb_o <= 1'b0;
    else if (pipeline_flush_i)
      wb_carry_wb_o <= 1'b0;
    else if (padv_wb_i)
      wb_carry_wb_o <= ocbo00[OCBT_CARRY_WB_POS];
    else
      wb_carry_wb_o <= 1'b0;
  end // @clock


  // WB delay slot
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_delay_slot_o <= 1'b0;
    else if (pipeline_flush_i)
      wb_delay_slot_o <= 1'b0;
    else if (padv_wb_i)
      wb_delay_slot_o <= ocbo00[OCBT_DELAY_SLOT_POS];
  end // @clock


  // address of D1 end D2 PC
  always @(posedge clk) begin
    if (padv_wb_i & ~pipeline_flush_i) begin
      wb_rfd1_adr_o <= {ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB], ocbo00[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB]};
      wb_rfd2_adr_o <=  ocbo00[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB];
      pc_wb_o       <=  pc_exec;
    end
  end // @clock

endmodule // mor1kx_oman_marocchino
