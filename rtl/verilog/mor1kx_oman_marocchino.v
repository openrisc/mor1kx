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
  parameter OPTION_RF_ADDR_WIDTH =  5
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
  input                                 dcod_op_fp32_arith_i,
  input                                 dcod_op_ls_i,     // load / store (we need store for pushing LSU exceptions)
  input                                 dcod_op_lsu_atomic_i,
  input                                 dcod_op_rfe_i,    // l.rfe

  // DECODE non-latched additional information related instruction
  //  part #1: iformation stored in order control buffer
  input                                 dcod_delay_slot_i, // instruction is in delay slot
  input                                 dcod_flag_await_i, // instruction is multi-cycle computation of flag
  input                                 dcod_flag_wb_i,    // instruction affects comparison flag
  input                                 dcod_carry_wb_i,   // instruction affects carry flag
  input                                 dcod_rf_wb_i,      // instruction generates WB
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfd_adr_i,    // WB address
  input      [OPTION_OPERAND_WIDTH-1:0] pc_decode_i,       // instruction virtual address
  //  part #2: information required for data dependancy detection
  input                                 dcod_rfa_req_i,    // instruction requires operand A
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa_adr_i,    // source of operand A
  input                                 dcod_rfb_req_i,    // instruction requires operand B
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb_adr_i,    // source of operand B
  input                                 dcod_flag_req_i,   // need comparison flag (l.cmov)
  input                                 dcod_carry_req_i,  // need carry flag
  input                                 dcod_op_jr_i,      // l.jr/l.jalr require operand B (potentially hazard)
  input                                 dcod_op_brcond_i,  // l.bf/l.bnf require awaited flag (stall fetch)
  //  part #3: information required for create enable for
  //           for external (timer/ethernet/uart/etc) interrupts
  input                                 dcod_op_lsu_store_i,
  input                                 dcod_op_mtspr_i,
  input                                 dcod_op_msync_i,
  //  part #4: for MF(T)SPR processing
  input                                 dcod_op_mfspr_i,

  // collect busy flags from execution modules
  input                                 op_1clk_busy_i,
  input                                 mul_busy_i,
  input                                 div_busy_i,
  input                                 fp32_arith_busy_i,
  input                                 lsu_busy_i,

  // collect valid flags from execution modules
  input                                 div_valid_i,
  input                                 mul_valid_i,
  input                                 fp32_arith_valid_i,
  input                                 lsu_valid_i,

  // FETCH & DECODE exceptions
  input                                 fetch_except_ibus_err_i,
  input                                 fetch_except_ipagefault_i,
  input                                 fetch_except_itlb_miss_i,
  input                                 fetch_except_ibus_align_i,
  input                                 dcod_except_illegal_i,
  input                                 dcod_except_syscall_i,
  input                                 dcod_except_trap_i,

  // EXECUTE-to-DECODE hazards
  output                                stall_fetch_o,
  output                                exe2dec_hazard_a_o,
  output                                exe2dec_hazard_b_o,

  // DECODE result could be processed by EXECUTE
  output                                dcod_valid_o,

  // EXECUTE completed (desired unit is ready)
  output                                exec_valid_o,

  // control WB latches of execution modules
  output                                grant_wb_to_1clk_o,
  output                                grant_wb_to_div_o,
  output                                grant_wb_to_mul_o,
  output                                grant_wb_to_fp32_arith_o,
  output                                grant_wb_to_lsu_o,
  // common flag signaling that WB ir required
  output                                do_rf_wb_o,

  // Support IBUS error handling in CTRL
  output                                exec_jump_or_branch_o,
  output     [OPTION_OPERAND_WIDTH-1:0] pc_exec_o,

  //   Flag to enabel/disable exterlal interrupts processing
  // depending on the fact is instructions restartable or not
  output                                exec_interrupts_en_o,

  // WB outputs
  //  ## instruction related information
  output reg [OPTION_OPERAND_WIDTH-1:0] pc_wb_o,
  output reg                            wb_delay_slot_o,
  output reg [OPTION_RF_ADDR_WIDTH-1:0] wb_rfd_adr_o,
  output reg                            wb_rf_wb_o,
  //  ## RFE processing
  output reg                            wb_op_rfe_o,
  //  ## output exceptions: IFETCH
  output reg                            wb_except_ibus_err_o,
  output reg                            wb_except_ipagefault_o,
  output reg                            wb_except_itlb_miss_o,
  output reg                            wb_except_ibus_align_o,
  //  ## output exceptions: DECODE
  output reg                            wb_except_illegal_o,
  output reg                            wb_except_syscall_o,
  output reg                            wb_except_trap_o,
  //  ## combined DECODE/IFETCH exceptions 
  output reg                            wb_fd_an_except_o
);

  // [O]rder [C]ontrol [B]uffer [T]ap layout
  //  [0...6] Exceptions generated by FETCH & DECODE.
  //          Pay atttention that LSU exceptions go to WB around order control buffer.
  //  [7] "A FETCH or DECODE exception" flag.
  //      FETCH & DECODE exceptions combined by OR to simplify logic for exception analysis.
  localparam  OCBT_FD_AN_EXCEPT_POS   = 7;
  //  Flag that external interrupt is enabled (instruction is re-startable)
  localparam  OCBT_INTERRUPTS_EN_POS  = OCBT_FD_AN_EXCEPT_POS   + 1;
  //  Unit wise requested/ready
  localparam  OCBT_OP_PASS_EXEC_POS   = OCBT_INTERRUPTS_EN_POS  + 1;
  localparam  OCBT_JUMP_OR_BRANCH_POS = OCBT_OP_PASS_EXEC_POS   + 1;
  localparam  OCBT_OP_1CLK_POS        = OCBT_JUMP_OR_BRANCH_POS + 1;
  localparam  OCBT_OP_DIV_POS         = OCBT_OP_1CLK_POS        + 1;
  localparam  OCBT_OP_MUL_POS         = OCBT_OP_DIV_POS         + 1;
  localparam  OCBT_OP_FP32_POS        = OCBT_OP_MUL_POS         + 1; // arithmetic part only, FP comparison is 1-clock
  localparam  OCBT_OP_LS_POS          = OCBT_OP_FP32_POS        + 1; // load / store (we need it for pushing LSU exceptions)
  localparam  OCBT_OP_LSU_ATOMIC_POS  = OCBT_OP_LS_POS          + 1;
  localparam  OCBT_OP_RFE_POS         = OCBT_OP_LSU_ATOMIC_POS  + 1; // l.rfe
  //  Instruction is in delay slot
  localparam  OCBT_DELAY_SLOT_POS     = OCBT_OP_RFE_POS         + 1;
  //  Instruction is multi-cycle computation of flag
  localparam  OCBT_FLAG_AWAIT_POS     = OCBT_DELAY_SLOT_POS     + 1;
  //  Instruction affect comparison flag
  localparam  OCBT_FLAG_WB_POS        = OCBT_FLAG_AWAIT_POS     + 1;
  //  Instruction affect carry flag
  localparam  OCBT_CARRY_WB_POS       = OCBT_FLAG_WB_POS        + 1;
  //  Instruction generates WB
  localparam  OCBT_RF_WB_POS          = OCBT_CARRY_WB_POS       + 1;
  localparam  OCBT_RFD_ADR_LSB        = OCBT_RF_WB_POS          + 1;
  localparam  OCBT_RFD_ADR_MSB        = OCBT_RF_WB_POS          + OPTION_RF_ADDR_WIDTH;
  //  Program counter
  localparam  OCBT_PC_LSB             = OCBT_RFD_ADR_MSB        + 1;
  localparam  OCBT_PC_MSB             = OCBT_RFD_ADR_MSB        + OPTION_OPERAND_WIDTH;
  //  value of MSB of order control buffer tap
  localparam  OCBT_MSB                = OCBT_PC_MSB;
  localparam  OCBT_WIDTH              = OCBT_MSB                + 1;


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


  // Combine FETCH related exceptions
  wire fetch_an_except = fetch_except_ibus_err_i  | fetch_except_ipagefault_i |
                         fetch_except_itlb_miss_i | fetch_except_ibus_align_i;
  // Combine DECODE related exceptions
  wire dcod_an_except = dcod_except_illegal_i | dcod_except_syscall_i |
                        dcod_except_trap_i;


  // input pack
  wire  [OCBT_MSB:0] ocbi;
  assign ocbi = { // various instruction related information
                  pc_decode_i,       // instruction virtual address
                  dcod_rfd_adr_i,    // WB address
                  dcod_rf_wb_i,      // instruction generates WB
                  dcod_carry_wb_i,   // istruction affects carry flag
                  dcod_flag_wb_i,    // istruction affects comparison flag
                  dcod_flag_await_i, // instruction is multi-cycle computation of flag
                  dcod_delay_slot_i, // istruction is in delay slot
                  // unit that must be granted for WB
                  dcod_op_rfe_i,     // l.rfe
                  (dcod_op_lsu_store_i & dcod_op_lsu_atomic_i), // l.swa affects flag
                  dcod_op_ls_i,      // load / store (we need it for pushing LSU exceptions)
                  dcod_op_fp32_arith_i,
                  dcod_op_mul_i,
                  dcod_op_div_i,
                  dcod_op_1clk_i,
                  dcod_jump_or_branch_i,
                  dcod_op_pass_exec_i,
                  // Flag that istruction is restartable
                  interrupts_en,
                  // combined FETCH & DECODE exceptions flag
                  (fetch_an_except | dcod_an_except),
                  // FETCH & DECODE exceptions
                  fetch_except_ibus_err_i,
                  fetch_except_ipagefault_i,
                  fetch_except_itlb_miss_i,
                  fetch_except_ibus_align_i,
                  dcod_except_illegal_i,
                  dcod_except_syscall_i,
                  dcod_except_trap_i };


  wire [OCBT_MSB:0] ocbo00, ocbo01, ocbo02, ocbo03,
                    ocbo04, ocbo05, ocbo06, ocbo07;

  wire ocb_full, ocb_empty;


  //-------------------------------//
  // Order Control Buffer instance //
  //-------------------------------//

  mor1kx_ocb_marocchino
  #(
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
    // data ouputs
    .ocbo00_o         (ocbo00), // OCB output (head)
    .ocbo01_o         (ocbo01), // ...
    .ocbo02_o         (ocbo02), // ...
    .ocbo03_o         (ocbo03), // ...
    .ocbo04_o         (ocbo04), // ...
    .ocbo05_o         (ocbo05), // ...
    .ocbo06_o         (ocbo06), // ...
    .ocbo07_o         (ocbo07)  // OCB entrance
  );


  // Grant WB-access to units
  assign grant_wb_to_1clk_o        = ocbo00[OCBT_OP_1CLK_POS];
  assign grant_wb_to_div_o         = ocbo00[OCBT_OP_DIV_POS];
  assign grant_wb_to_mul_o         = ocbo00[OCBT_OP_MUL_POS];
  assign grant_wb_to_fp32_arith_o  = ocbo00[OCBT_OP_FP32_POS];
  assign grant_wb_to_lsu_o         = ocbo00[OCBT_OP_LS_POS];
  // common flag signaling that WB is required
  assign do_rf_wb_o                = ocbo00[OCBT_RF_WB_POS];

  // EXECUTE-to-DECODE hazards
  //  # WB address and flag
  wire [OPTION_RF_ADDR_WIDTH-1:0] exec_rfd_adr = ocbo00[OCBT_RFD_ADR_MSB:OCBT_RFD_ADR_LSB];
  wire                            exec_rf_wb   = ocbo00[OCBT_RF_WB_POS];
  //  # Hazard by operand A
  assign exe2dec_hazard_a_o = exec_rf_wb & dcod_rfa_req_i & (exec_rfd_adr == dcod_rfa_adr_i);
  //  # Hazard by operand B
  assign exe2dec_hazard_b_o = exec_rf_wb & dcod_rfb_req_i & (exec_rfd_adr == dcod_rfb_adr_i);


  //   An execute module is ready and granted access to WB
  //   Instructions l.mf(t)spr have got guaranted WB access because
  // no any new instruction is issued into execution till
  // l.mf(t)spr has been completed. Pay attention that we start
  // l.mf(t)spr ecxecution after completion of all peviously
  // issued instructions only.
  //   l.rfe and FETCH/DECODE exceptions are also should
  // push WB latches
  assign exec_valid_o = ocbo00[OCBT_OP_1CLK_POS] |
                        (div_valid_i & ocbo00[OCBT_OP_DIV_POS]) |
                        (mul_valid_i & ocbo00[OCBT_OP_MUL_POS]) |
                        (fp32_arith_valid_i & ocbo00[OCBT_OP_FP32_POS]) |
                        (lsu_valid_i & ocbo00[OCBT_OP_LS_POS]) |
                        ocbo00[OCBT_OP_PASS_EXEC_POS] | // also includes l.rfe in the sense
                        ocbo00[OCBT_FD_AN_EXCEPT_POS];


  // waiting EXECUTE result (only multicycle instructions make sense)
  wire exec_waiting = (~div_valid_i & ocbo00[OCBT_OP_DIV_POS]) |
                      (~mul_valid_i & ocbo00[OCBT_OP_MUL_POS]) |
                      (~fp32_arith_valid_i & ocbo00[OCBT_OP_FP32_POS]) |
                      (~lsu_valid_i & ocbo00[OCBT_OP_LS_POS]);

  // DECODE stall components
  //  stall by unit usage hazard
  //     (unit could be either busy or waiting for WB access)
  wire stall_by_hazard_u =
    (dcod_op_1clk_i & op_1clk_busy_i) |
    (dcod_op_div_i  & div_busy_i) |
    (dcod_op_mul_i  & mul_busy_i) |
    (dcod_op_fp32_arith_i & (fp32_arith_busy_i | (fp32_arith_valid_i & ~ocbo00[OCBT_OP_FP32_POS]))) |
    ((dcod_op_ls_i | dcod_op_msync_i) & lsu_busy_i);

  //  stall by operand A hazard
  //    hazard has occured inside OCB
  wire ocb_hazard_a = dcod_rfa_req_i &
    ((ocbo07[OCBT_RF_WB_POS] & (ocbo07[OCBT_RFD_ADR_MSB:OCBT_RFD_ADR_LSB] == dcod_rfa_adr_i)) |
     (ocbo06[OCBT_RF_WB_POS] & (ocbo06[OCBT_RFD_ADR_MSB:OCBT_RFD_ADR_LSB] == dcod_rfa_adr_i)) |
     (ocbo05[OCBT_RF_WB_POS] & (ocbo05[OCBT_RFD_ADR_MSB:OCBT_RFD_ADR_LSB] == dcod_rfa_adr_i)) |
     (ocbo04[OCBT_RF_WB_POS] & (ocbo04[OCBT_RFD_ADR_MSB:OCBT_RFD_ADR_LSB] == dcod_rfa_adr_i)) |
     (ocbo03[OCBT_RF_WB_POS] & (ocbo03[OCBT_RFD_ADR_MSB:OCBT_RFD_ADR_LSB] == dcod_rfa_adr_i)) |
     (ocbo02[OCBT_RF_WB_POS] & (ocbo02[OCBT_RFD_ADR_MSB:OCBT_RFD_ADR_LSB] == dcod_rfa_adr_i)) |
     (ocbo01[OCBT_RF_WB_POS] & (ocbo01[OCBT_RFD_ADR_MSB:OCBT_RFD_ADR_LSB] == dcod_rfa_adr_i)));
  //    combine with DECODE-to-EXECUTE hazard
  wire stall_by_hazard_a = ocb_hazard_a | (exe2dec_hazard_a_o & exec_waiting);

  //  stall by operand B hazard
  //    hazard has occured inside OCB
  wire ocb_hazard_b = dcod_rfb_req_i &
    ((ocbo07[OCBT_RF_WB_POS] & (ocbo07[OCBT_RFD_ADR_MSB:OCBT_RFD_ADR_LSB] == dcod_rfb_adr_i)) |
     (ocbo06[OCBT_RF_WB_POS] & (ocbo06[OCBT_RFD_ADR_MSB:OCBT_RFD_ADR_LSB] == dcod_rfb_adr_i)) |
     (ocbo05[OCBT_RF_WB_POS] & (ocbo05[OCBT_RFD_ADR_MSB:OCBT_RFD_ADR_LSB] == dcod_rfb_adr_i)) |
     (ocbo04[OCBT_RF_WB_POS] & (ocbo04[OCBT_RFD_ADR_MSB:OCBT_RFD_ADR_LSB] == dcod_rfb_adr_i)) |
     (ocbo03[OCBT_RF_WB_POS] & (ocbo03[OCBT_RFD_ADR_MSB:OCBT_RFD_ADR_LSB] == dcod_rfb_adr_i)) |
     (ocbo02[OCBT_RF_WB_POS] & (ocbo02[OCBT_RFD_ADR_MSB:OCBT_RFD_ADR_LSB] == dcod_rfb_adr_i)) |
     (ocbo01[OCBT_RF_WB_POS] & (ocbo01[OCBT_RFD_ADR_MSB:OCBT_RFD_ADR_LSB] == dcod_rfb_adr_i)));
  //    combine with DECODE-to-EXECUTE hazard
  wire stall_by_hazard_b = ocb_hazard_b | (exe2dec_hazard_b_o & (exec_waiting | dcod_op_jr_i));

  //  stall by comparison flag hazard
  //    hazard has occured inside OCB
  wire ocb_flag = ocbo07[OCBT_FLAG_WB_POS] | ocbo06[OCBT_FLAG_WB_POS] | ocbo05[OCBT_FLAG_WB_POS] |
                  ocbo04[OCBT_FLAG_WB_POS] | ocbo03[OCBT_FLAG_WB_POS] | ocbo02[OCBT_FLAG_WB_POS] |
                  ocbo01[OCBT_FLAG_WB_POS];
  //    waiting completion of atomic instruction (others WB-flag instructions are 1-clk)
  wire flag_waiting = ~lsu_valid_i & ocbo00[OCBT_OP_LSU_ATOMIC_POS];
  //    combine with DECODE-to-EXECUTE hazard
  wire stall_by_flag = dcod_flag_req_i & (ocb_flag | flag_waiting);

  //  stall by carry flag hazard
  //    hazard has occured inside OCB
  wire ocb_carry = ocbo07[OCBT_CARRY_WB_POS] | ocbo06[OCBT_CARRY_WB_POS] | ocbo05[OCBT_CARRY_WB_POS] |
                   ocbo04[OCBT_CARRY_WB_POS] | ocbo03[OCBT_CARRY_WB_POS] | ocbo02[OCBT_CARRY_WB_POS] |
                   ocbo01[OCBT_CARRY_WB_POS];
  //    waiting completion of DIV instruction (others WB-carry instructions are 1-clk)
  wire carry_waiting = ~div_valid_i & ocbo00[OCBT_OP_DIV_POS];
  //    combine with DECODE-to-EXECUTE hazard
  wire stall_by_carry = dcod_carry_req_i & (ocb_carry | carry_waiting);

  //  stall by:
  //    a) MF(T)SPR in decode till and OCB become empty (see here)
  //    b) till completion MF(T)SPR (see CTRL)
  //       this completion generates padv-wb,
  //       in next turn padv-wb cleans up OCB and restores
  //       instructions issue
  wire stall_by_mXspr = (dcod_op_mtspr_i | dcod_op_mfspr_i) & ~ocb_empty;

  // combine stalls to decode-valid flag
  assign dcod_valid_o = ~stall_by_hazard_u & ~ocb_full          &
                        ~stall_by_hazard_a & ~stall_by_hazard_b &
                        ~stall_by_flag     & ~stall_by_carry    &
                        ~stall_by_mXspr;


  //   Stall FETCH advance (CTRL).
  //   a) Detect the situation where there is a jump to register in decode
  // stage and an instruction in execute stage that will write to that
  // register.
  //   b) l.bf/l.bnf waiting flag if it should be computed by multi-cycle
  //      instruction like l.swa of float64 comparison.
  //      MAROCCHINO_TODO: performance improvement is possible with
  //                       forwarding of result of these instructions. 
  //   c) When an l.rfe/ecxeptions are in decode stage.
  // The main purpose of this is waiting till l.rfe/exceptions propagate
  // up to WB stage.
  //   d) And the final reason to stop FETCH is l.mf(t)spr execution.
  //
  // auxiliary
  wire flag_await = ocbo07[OCBT_FLAG_AWAIT_POS] | ocbo06[OCBT_FLAG_AWAIT_POS] | ocbo05[OCBT_FLAG_AWAIT_POS] |
                    ocbo04[OCBT_FLAG_AWAIT_POS] | ocbo03[OCBT_FLAG_AWAIT_POS] | ocbo02[OCBT_FLAG_AWAIT_POS] |
                    ocbo01[OCBT_FLAG_AWAIT_POS] | ocbo00[OCBT_FLAG_AWAIT_POS];
  // stall fetch combination
  assign stall_fetch_o = ((ocb_hazard_b | exe2dec_hazard_b_o) & dcod_op_jr_i) | // stall FETCH
                         (flag_await & dcod_op_brcond_i) |                      // stall FETCH
                         dcod_op_rfe_i | dcod_an_except;                        // stall FETCH


  // Support IBUS error handling in CTRL
  assign exec_jump_or_branch_o = ocbo00[OCBT_JUMP_OR_BRANCH_POS];
  assign pc_exec_o             = ocbo00[OCBT_PC_MSB:OCBT_PC_LSB];

  //   Flag to enabel/disable exterlal interrupts processing
  // depending on the fact is instructions restartable or not
  assign exec_interrupts_en_o = ocbo00[OCBT_INTERRUPTS_EN_POS];


  // WB-request (1-clock to prevent extra writes in RF)
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_rf_wb_o <= 1'b0;
    else if (pipeline_flush_i)
      wb_rf_wb_o <= 1'b0;
    else if (padv_wb_i)
      wb_rf_wb_o <= exec_rf_wb;
    else
      wb_rf_wb_o <= 1'b0;
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


  // address of destination register & PC
  always @(posedge clk) begin
    if (padv_wb_i & ~pipeline_flush_i) begin
      wb_rfd_adr_o <= exec_rfd_adr;
      pc_wb_o      <= ocbo00[OCBT_PC_MSB:OCBT_PC_LSB];
    end
  end // @clock


  // WB EXCEPTIONS (excluding LSU's) & RFE
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      // RFE
      wb_op_rfe_o            <= 1'b0;
      // FETCH/DECODE exceptions
      wb_except_ibus_err_o   <= 1'b0;
      wb_except_ipagefault_o <= 1'b0;
      wb_except_itlb_miss_o  <= 1'b0;
      wb_except_ibus_align_o <= 1'b0;
      // DECODE exceptions
      wb_except_illegal_o    <= 1'b0;
      wb_except_syscall_o    <= 1'b0;
      wb_except_trap_o       <= 1'b0;
      // Combined DECODE/IFETCH exceptions 
      wb_fd_an_except_o      <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      // RFE
      wb_op_rfe_o            <= 1'b0;
      // IFETCH exceptions
      wb_except_ibus_err_o   <= 1'b0;
      wb_except_ipagefault_o <= 1'b0;
      wb_except_itlb_miss_o  <= 1'b0;
      wb_except_ibus_align_o <= 1'b0;
      // DECODE exceptions
      wb_except_illegal_o    <= 1'b0;
      wb_except_syscall_o    <= 1'b0;
      wb_except_trap_o       <= 1'b0;
      // Combined DECODE/IFETCH exceptions 
      wb_fd_an_except_o      <= 1'b0;
    end
    else if (padv_wb_i) begin
      // RFE
      wb_op_rfe_o            <= ocbo00[OCBT_OP_RFE_POS];
      // IFETCH exceptions
      wb_except_ibus_err_o   <= ocbo00[6];
      wb_except_ipagefault_o <= ocbo00[5];
      wb_except_itlb_miss_o  <= ocbo00[4];
      wb_except_ibus_align_o <= ocbo00[3];
      // DECODE exceptions
      wb_except_illegal_o    <= ocbo00[2];
      wb_except_syscall_o    <= ocbo00[1];
      wb_except_trap_o       <= ocbo00[0];
      // Combined DECODE/IFETCH exceptions 
      wb_fd_an_except_o      <= ocbo00[OCBT_FD_AN_EXCEPT_POS];
    end
  end // @clock

endmodule // mor1kx_oman_marocchino
