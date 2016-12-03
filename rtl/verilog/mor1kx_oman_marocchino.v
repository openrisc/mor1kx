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
  parameter DEST_FLAG_ADDR_WIDTH =  3  // log2(Re-Ordering buffer width)
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
  input                                 dcod_rfa1_req_i,     // instruction requires operand A
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa1_adr_i,     // source of operand A
  input                                 dcod_rfb1_req_i,     // instruction requires operand B
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb1_adr_i,     // source of operand B
  input                                 dcod_flag_req_i,    // need comparison flag (l.cmov)
  input                                 dcod_carry_req_i,   // need carry flag
  input                                 dcod_op_jr_i,       // l.jr/l.jalr require operand B (potentially hazard)
  input                                 dcod_op_brcond_i,   // l.bf/l.bnf require awaited flag (stall fetch)
  input                                 busy_op_1clk_cmp_i, // 1-clk flag not computed yet (stall fetch)
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

  // collect valid flags from execution modules
  input                                 div_valid_i,
  input                                 mul_valid_i,
  input                                 fpxx_arith_valid_i,
  input                                 lsu_valid_i,

  // FETCH & DECODE exceptions
  input                                 fetch_except_ibus_err_i,
  input                                 fetch_except_ipagefault_i,
  input                                 fetch_except_itlb_miss_i,
  input                                 fetch_except_ibus_align_i,
  input                                 dcod_except_illegal_i,
  input                                 dcod_except_syscall_i,
  input                                 dcod_except_trap_i,

  // OMAN-to-DECODE hazards
  //  combined flag
  output                                omn2dec_a_hazard_lsu_o,
  output                                omn2dec_a_hazard_1clk_o,
  output                                omn2dec_a_hazard_mclk_o,
  //  by FLAG and CARRY
  output                                busy_hazard_f_o,
  output     [DEST_FLAG_ADDR_WIDTH-1:0] busy_hazard_f_adr_o,
  output                                busy_hazard_c_o,
  output     [DEST_FLAG_ADDR_WIDTH-1:0] busy_hazard_c_adr_o,
  //  by operands
  output                                busy_hazard_d1a1_o,
  output      [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_d1a1_adr_o,
  output                                busy_hazard_d1b1_o,
  output      [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_d1b1_adr_o,
  output                                busy_hazard_d2a1_o,
  output      [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_d2a1_adr_o,
  output                                busy_hazard_d2b1_o,
  output      [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_d2b1_adr_o,
  output                                busy_hazard_d1a2_o,
  output      [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_d1a2_adr_o,
  output                                busy_hazard_d1b2_o,
  output      [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_d1b2_adr_o,
  output                                busy_hazard_d2a2_o,
  output      [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_d2a2_adr_o,
  output                                busy_hazard_d2b2_o,
  output      [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_d2b2_adr_o,

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
  output                                exec_flag_wb_o,
  output                                exec_carry_wb_o,
  output     [DEST_FLAG_ADDR_WIDTH-1:0] exec_flag_carry_adr_o,
  output                                exec_rfd1_wb_o,
  output      [DEST_REG_ADDR_WIDTH-1:0] exec_rfd1_adr_o,
  // for FPU64
  output                                exec_rfd2_wb_o,
  output      [DEST_REG_ADDR_WIDTH-1:0] exec_rfd2_adr_o,

  // Stall fetch by specific type of hazards
  output                                stall_fetch_o,
  // Signal to FETCH that target address or flag isn't ready
  output                                fetch_waiting_target_o,

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
  output reg  [DEST_REG_ADDR_WIDTH-1:0] wb_rfd1_adr_o,
  output reg                            wb_rfd1_wb_o,
  output reg                            wb_flag_wb_o,
  output reg                            wb_carry_wb_o,
  output reg [DEST_FLAG_ADDR_WIDTH-1:0] wb_flag_carry_adr_o,
  // for FPU64
  output      [DEST_REG_ADDR_WIDTH-1:0] wb_rfd2_adr_o,
  output                                wb_rfd2_wb_o,
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
  localparam  OCBT_OP_FPXX_ARITH_POS  = OCBT_OP_MUL_POS         + 1; // arithmetic part only, FP comparison is 1-clock
  localparam  OCBT_OP_LS_POS          = OCBT_OP_FPXX_ARITH_POS  + 1; // load / store (we need it for pushing LSU exceptions)
  localparam  OCBT_OP_RFE_POS         = OCBT_OP_LS_POS          + 1; // l.rfe
  //  Instruction is in delay slot
  localparam  OCBT_DELAY_SLOT_POS     = OCBT_OP_RFE_POS         + 1;
  //  Instruction writting comparison flag
  localparam  OCBT_FLAG_WB_POS        = OCBT_DELAY_SLOT_POS     + 1; // any such instruction
  localparam  OCBT_FLAG_WB_MCYCLE_POS = OCBT_FLAG_WB_POS        + 1; // such istruction is multi-cycle (l.swa, lf.sf*.d)
  //  Instruction writting carry flag
  localparam  OCBT_CARRY_WB_POS       = OCBT_FLAG_WB_MCYCLE_POS + 1;
  //  Instruction generates WB
  localparam  OCBT_RFD1_WB_POS        = OCBT_CARRY_WB_POS       + 1;
  localparam  OCBT_RFD1_ADR_LSB       = OCBT_RFD1_WB_POS        + 1;
  localparam  OCBT_RFD1_ADR_MSB       = OCBT_RFD1_WB_POS        + OPTION_RF_ADDR_WIDTH;
  //  Extention to address of RFD, FLAG and CARRY
  localparam  OCBT_EXT_ADR_LSB        = OCBT_RFD1_ADR_MSB       + 1;
  localparam  OCBT_EXT_ADR_MSB        = OCBT_RFD1_ADR_MSB       + DEST_FLAG_ADDR_WIDTH;
  //  Program counter
  localparam  OCBT_PC_LSB             = OCBT_EXT_ADR_MSB        + 1;
  localparam  OCBT_PC_MSB             = OCBT_EXT_ADR_MSB        + OPTION_OPERAND_WIDTH;
  //  value of MSB of order control buffer tap
  localparam  OCBT_MSB                = OCBT_PC_MSB;
  localparam  OCBT_WIDTH              = OCBT_MSB                + 1;


  // Generator of extension bits for register renaming
  reg [DEST_FLAG_ADDR_WIDTH-1:0] ext_bits_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      ext_bits_r <= {DEST_FLAG_ADDR_WIDTH{1'b0}};
    else if (pipeline_flush_i)
      ext_bits_r <= {DEST_FLAG_ADDR_WIDTH{1'b0}};
    else if (padv_decode_i)
      ext_bits_r <= ext_bits_r + 1'b1;
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


  // Combine FETCH related exceptions
  wire fetch_an_except = fetch_except_ibus_err_i  | fetch_except_ipagefault_i |
                         fetch_except_itlb_miss_i | fetch_except_ibus_align_i;
  // Combine DECODE related exceptions
  wire dcod_an_except = dcod_except_illegal_i | dcod_except_syscall_i |
                        dcod_except_trap_i;


  // input pack
  wire  [OCBT_MSB:0] ocbi;
  assign ocbi = { // various instruction related information
                  pc_decode_i,            // instruction virtual address
                  ext_bits_r,             // extension to RFD, FLAG or CARRY
                  dcod_rfd1_adr_i,        // WB address
                  dcod_rfd1_wb_i,         // instruction generates WB
                  dcod_carry_wb_i,        // istruction affects carry flag
                  dcod_flag_wb_mcycle_i,  // the multy-cycle instruction affects comparison flag
                  dcod_flag_wb_i,         // any instruction which affects comparison flag
                  dcod_delay_slot_i,      // istruction is in delay slot
                  // unit that must be granted for WB
                  dcod_op_rfe_i,     // l.rfe
                  dcod_op_ls_i,      // load / store (we need it for pushing LSU exceptions)
                  dcod_op_fpxx_arith_i,
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


  //--------------------------------------------//
  // Order Control Buffer for FPU64 Additionals //
  //------------------------------------------- //

  localparam  OCBT_OP_FP64_CMP_POS   = 0; // source for granting write back to fp64 comparison
  localparam  OCBT_OP_FP64_ARITH_POS = OCBT_OP_FP64_CMP_POS   + 1;   // it is also source for *_rf_wb2
  localparam  OCBT_RFD2_ADR_LSB      = OCBT_OP_FP64_ARITH_POS + 1;
  localparam  OCBT_RFD2_ADR_MSB      = OCBT_OP_FP64_ARITH_POS + OPTION_RF_ADDR_WIDTH;
  // whole FP64 OCB width and MSB
  localparam  OCBT_FP64_MSB          = OCBT_RFD2_ADR_MSB;
  localparam  OCBT_FP64_WIDTH        = OCBT_FP64_MSB          + 1;

  // alias for *_rf_wb2
  localparam  OCBT_RFD2_WB_POS       = OCBT_OP_FP64_ARITH_POS;

  // for FPU's 64 bits data: historycally separated from 32-bit OCB
  // MAROCCHINNO_TODO: merge it into 32-bit OCB
  wire [OCBT_FP64_MSB:0] fp64_ocbi;
  // input pack
  assign fp64_ocbi = { dcod_rfd2_adr_i,
                       (dcod_op_fpxx_arith_i & dcod_op_fp64_arith_i),
                       dcod_op_fp64_cmp_i };
  // buffer outputs
  wire [OCBT_FP64_MSB:0] fp64_ocbo00, fp64_ocbo01, fp64_ocbo02, fp64_ocbo03,
                         fp64_ocbo04, fp64_ocbo05, fp64_ocbo06, fp64_ocbo07;
  // buffer instance
  mor1kx_ocb_marocchino
  #(
    .DATA_SIZE  (OCBT_FP64_WIDTH)
  )
  u_ocbfp64
  (
    // clocks, resets and other input controls
    .clk              (clk), // OCBT_FP64
    .rst              (rst), // OCBT_FP64
    .pipeline_flush_i (pipeline_flush_i), // OCBT_FP64
    .padv_decode_i    (padv_decode_i), // OCBT_FP64
    .padv_wb_i        (padv_wb_i), // OCBT_FP64
    // data input
    .ocbi_i           (fp64_ocbi), // OCBT_FP64
    // "OCB is empty" and "full" flags
    .empty_o          (), // OCBT_FP64
    .full_o           (), // OCBT_FP64
    // data ouputs
    .ocbo00_o         (fp64_ocbo00), // OCBT_FP64 OCB output (head)
    .ocbo01_o         (fp64_ocbo01), // OCBT_FP64 ...
    .ocbo02_o         (fp64_ocbo02), // OCBT_FP64 ...
    .ocbo03_o         (fp64_ocbo03), // OCBT_FP64 ...
    .ocbo04_o         (fp64_ocbo04), // OCBT_FP64 ...
    .ocbo05_o         (fp64_ocbo05), // OCBT_FP64 ...
    .ocbo06_o         (fp64_ocbo06), // OCBT_FP64 ...
    .ocbo07_o         (fp64_ocbo07)  // OCBT_FP64 OCB entrance
  );



  // Grant WB-access to units
  assign grant_wb_to_1clk_o        = ocbo00[OCBT_OP_1CLK_POS];
  assign grant_wb_to_div_o         = ocbo00[OCBT_OP_DIV_POS];
  assign grant_wb_to_mul_o         = ocbo00[OCBT_OP_MUL_POS];
  assign grant_wb_to_fpxx_arith_o  = ocbo00[OCBT_OP_FPXX_ARITH_POS];
  assign grant_wb_to_lsu_o         = ocbo00[OCBT_OP_LS_POS];
  assign grant_wb_to_fp64_cmp_o    = fp64_ocbo00[OCBT_OP_FP64_CMP_POS];


  // D1A1
  wire ocbo07_hazard_d1a1 = ocbo07[OCBT_RFD1_WB_POS] & (ocbo07[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa1_adr_i);
  wire ocbo06_hazard_d1a1 = ocbo06[OCBT_RFD1_WB_POS] & (ocbo06[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa1_adr_i);
  wire ocbo05_hazard_d1a1 = ocbo05[OCBT_RFD1_WB_POS] & (ocbo05[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa1_adr_i);
  wire ocbo04_hazard_d1a1 = ocbo04[OCBT_RFD1_WB_POS] & (ocbo04[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa1_adr_i);
  wire ocbo03_hazard_d1a1 = ocbo03[OCBT_RFD1_WB_POS] & (ocbo03[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa1_adr_i);
  wire ocbo02_hazard_d1a1 = ocbo02[OCBT_RFD1_WB_POS] & (ocbo02[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa1_adr_i);
  wire ocbo01_hazard_d1a1 = ocbo01[OCBT_RFD1_WB_POS] & (ocbo01[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa1_adr_i);
  // OMAN-to-DECODE hazard D1A1
  wire omn2dec_hazard_d1a1 = dcod_rfa1_req_i &
                             (ocbo07_hazard_d1a1 | ocbo06_hazard_d1a1 | ocbo05_hazard_d1a1 |
                              ocbo04_hazard_d1a1 | ocbo03_hazard_d1a1 | ocbo02_hazard_d1a1 |
                              ocbo01_hazard_d1a1);
  // Reservation station busy D1A1
  wire [DEST_FLAG_ADDR_WIDTH-1:0] hazard_d1a1_ext;
  assign hazard_d1a1_ext = ocbo07_hazard_d1a1 ? ocbo07[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo06_hazard_d1a1 ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo05_hazard_d1a1 ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo04_hazard_d1a1 ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo03_hazard_d1a1 ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo02_hazard_d1a1 ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo01_hazard_d1a1 ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB];
  assign busy_hazard_d1a1_o     = omn2dec_hazard_d1a1 | exe2dec_hazard_d1a1_o;
  assign busy_hazard_d1a1_adr_o = {hazard_d1a1_ext, dcod_rfa1_adr_i};


  // D1B1
  wire ocbo07_hazard_d1b1 = ocbo07[OCBT_RFD1_WB_POS] & (ocbo07[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb1_adr_i);
  wire ocbo06_hazard_d1b1 = ocbo06[OCBT_RFD1_WB_POS] & (ocbo06[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb1_adr_i);
  wire ocbo05_hazard_d1b1 = ocbo05[OCBT_RFD1_WB_POS] & (ocbo05[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb1_adr_i);
  wire ocbo04_hazard_d1b1 = ocbo04[OCBT_RFD1_WB_POS] & (ocbo04[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb1_adr_i);
  wire ocbo03_hazard_d1b1 = ocbo03[OCBT_RFD1_WB_POS] & (ocbo03[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb1_adr_i);
  wire ocbo02_hazard_d1b1 = ocbo02[OCBT_RFD1_WB_POS] & (ocbo02[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb1_adr_i);
  wire ocbo01_hazard_d1b1 = ocbo01[OCBT_RFD1_WB_POS] & (ocbo01[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb1_adr_i);
  // OMAN-to-DECODE hazard D1B1
  wire omn2dec_hazard_d1b1 = dcod_rfb1_req_i &
                             (ocbo07_hazard_d1b1 | ocbo06_hazard_d1b1 | ocbo05_hazard_d1b1 |
                              ocbo04_hazard_d1b1 | ocbo03_hazard_d1b1 | ocbo02_hazard_d1b1 |
                              ocbo01_hazard_d1b1);
  // Reservation station busy D1B1
  wire [DEST_FLAG_ADDR_WIDTH-1:0] hazard_d1b1_ext;
  assign hazard_d1b1_ext = ocbo07_hazard_d1b1 ? ocbo07[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo06_hazard_d1b1 ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo05_hazard_d1b1 ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo04_hazard_d1b1 ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo03_hazard_d1b1 ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo02_hazard_d1b1 ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo01_hazard_d1b1 ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB];
  assign busy_hazard_d1b1_o     = omn2dec_hazard_d1b1 | exe2dec_hazard_d1b1_o;
  assign busy_hazard_d1b1_adr_o = {hazard_d1b1_ext, dcod_rfb1_adr_i};


  // D2A1
  wire fp64_ocbo07_hazard_d2a1 = fp64_ocbo07[OCBT_RFD2_WB_POS] & (fp64_ocbo07[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa1_adr_i);
  wire fp64_ocbo06_hazard_d2a1 = fp64_ocbo06[OCBT_RFD2_WB_POS] & (fp64_ocbo06[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa1_adr_i);
  wire fp64_ocbo05_hazard_d2a1 = fp64_ocbo05[OCBT_RFD2_WB_POS] & (fp64_ocbo05[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa1_adr_i);
  wire fp64_ocbo04_hazard_d2a1 = fp64_ocbo04[OCBT_RFD2_WB_POS] & (fp64_ocbo04[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa1_adr_i);
  wire fp64_ocbo03_hazard_d2a1 = fp64_ocbo03[OCBT_RFD2_WB_POS] & (fp64_ocbo03[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa1_adr_i);
  wire fp64_ocbo02_hazard_d2a1 = fp64_ocbo02[OCBT_RFD2_WB_POS] & (fp64_ocbo02[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa1_adr_i);
  wire fp64_ocbo01_hazard_d2a1 = fp64_ocbo01[OCBT_RFD2_WB_POS] & (fp64_ocbo01[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa1_adr_i);
  // OMAN-to-DECODE hazard D2A1
  wire omn2dec_hazard_d2a1 = dcod_rfa1_req_i &
                             (fp64_ocbo07_hazard_d2a1 | fp64_ocbo06_hazard_d2a1 | fp64_ocbo05_hazard_d2a1 |
                              fp64_ocbo04_hazard_d2a1 | fp64_ocbo03_hazard_d2a1 | fp64_ocbo02_hazard_d2a1 |
                              fp64_ocbo01_hazard_d2a1);
  // Reservation station busy D2A1
  wire [DEST_FLAG_ADDR_WIDTH-1:0] hazard_d2a1_ext;
  assign hazard_d2a1_ext = fp64_ocbo07_hazard_d2a1 ? ocbo07[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo06_hazard_d2a1 ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo05_hazard_d2a1 ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo04_hazard_d2a1 ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo03_hazard_d2a1 ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo02_hazard_d2a1 ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo01_hazard_d2a1 ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                     ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB];
  assign busy_hazard_d2a1_o     = omn2dec_hazard_d2a1 | exe2dec_hazard_d2a1_o;
  assign busy_hazard_d2a1_adr_o = {hazard_d2a1_ext, dcod_rfa1_adr_i};


  // D2B1
  wire fp64_ocbo07_hazard_d2b1 = fp64_ocbo07[OCBT_RFD2_WB_POS] & (fp64_ocbo07[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb1_adr_i);
  wire fp64_ocbo06_hazard_d2b1 = fp64_ocbo06[OCBT_RFD2_WB_POS] & (fp64_ocbo06[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb1_adr_i);
  wire fp64_ocbo05_hazard_d2b1 = fp64_ocbo05[OCBT_RFD2_WB_POS] & (fp64_ocbo05[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb1_adr_i);
  wire fp64_ocbo04_hazard_d2b1 = fp64_ocbo04[OCBT_RFD2_WB_POS] & (fp64_ocbo04[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb1_adr_i);
  wire fp64_ocbo03_hazard_d2b1 = fp64_ocbo03[OCBT_RFD2_WB_POS] & (fp64_ocbo03[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb1_adr_i);
  wire fp64_ocbo02_hazard_d2b1 = fp64_ocbo02[OCBT_RFD2_WB_POS] & (fp64_ocbo02[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb1_adr_i);
  wire fp64_ocbo01_hazard_d2b1 = fp64_ocbo01[OCBT_RFD2_WB_POS] & (fp64_ocbo01[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb1_adr_i);
  // OMAN-to-DECODE hazard D2B1
  wire omn2dec_hazard_d2b1 = dcod_rfb1_req_i &
                             (fp64_ocbo07_hazard_d2b1 | fp64_ocbo06_hazard_d2b1 | fp64_ocbo05_hazard_d2b1 |
                              fp64_ocbo04_hazard_d2b1 | fp64_ocbo03_hazard_d2b1 | fp64_ocbo02_hazard_d2b1 |
                              fp64_ocbo01_hazard_d2b1);
  // Reservation station busy D2B1
  wire [DEST_FLAG_ADDR_WIDTH-1:0] hazard_d2b1_ext;
  assign hazard_d2b1_ext = fp64_ocbo07_hazard_d2b1 ? ocbo07[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo06_hazard_d2b1 ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo05_hazard_d2b1 ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo04_hazard_d2b1 ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo03_hazard_d2b1 ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo02_hazard_d2b1 ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo01_hazard_d2b1 ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                     ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB];
  assign busy_hazard_d2b1_o     = omn2dec_hazard_d2b1 | exe2dec_hazard_d2b1_o;
  assign busy_hazard_d2b1_adr_o = {hazard_d2b1_ext, dcod_rfb1_adr_i};


  // D1A2
  wire ocbo07_hazard_d1a2 = ocbo07[OCBT_RFD1_WB_POS] & (ocbo07[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa2_adr_i);
  wire ocbo06_hazard_d1a2 = ocbo06[OCBT_RFD1_WB_POS] & (ocbo06[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa2_adr_i);
  wire ocbo05_hazard_d1a2 = ocbo05[OCBT_RFD1_WB_POS] & (ocbo05[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa2_adr_i);
  wire ocbo04_hazard_d1a2 = ocbo04[OCBT_RFD1_WB_POS] & (ocbo04[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa2_adr_i);
  wire ocbo03_hazard_d1a2 = ocbo03[OCBT_RFD1_WB_POS] & (ocbo03[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa2_adr_i);
  wire ocbo02_hazard_d1a2 = ocbo02[OCBT_RFD1_WB_POS] & (ocbo02[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa2_adr_i);
  wire ocbo01_hazard_d1a2 = ocbo01[OCBT_RFD1_WB_POS] & (ocbo01[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa2_adr_i);
  // OMAN-to-DECODE hazard D1A2
  wire omn2dec_hazard_d1a2 = dcod_rfa2_req_i &
                             (ocbo07_hazard_d1a2 | ocbo06_hazard_d1a2 | ocbo05_hazard_d1a2 |
                              ocbo04_hazard_d1a2 | ocbo03_hazard_d1a2 | ocbo02_hazard_d1a2 |
                              ocbo01_hazard_d1a2);
  // Reservation station busy D1A2
  wire [DEST_FLAG_ADDR_WIDTH-1:0] hazard_d1a2_ext;
  assign hazard_d1a2_ext = ocbo07_hazard_d1a2 ? ocbo07[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo06_hazard_d1a2 ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo05_hazard_d1a2 ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo04_hazard_d1a2 ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo03_hazard_d1a2 ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo02_hazard_d1a2 ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo01_hazard_d1a2 ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB];
  assign busy_hazard_d1a2_o     = omn2dec_hazard_d1a2 | exe2dec_hazard_d1a2_o;
  assign busy_hazard_d1a2_adr_o = {hazard_d1a2_ext, dcod_rfa2_adr_i};


  // D1B2
  wire ocbo07_hazard_d1b2 = ocbo07[OCBT_RFD1_WB_POS] & (ocbo07[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb2_adr_i);
  wire ocbo06_hazard_d1b2 = ocbo06[OCBT_RFD1_WB_POS] & (ocbo06[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb2_adr_i);
  wire ocbo05_hazard_d1b2 = ocbo05[OCBT_RFD1_WB_POS] & (ocbo05[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb2_adr_i);
  wire ocbo04_hazard_d1b2 = ocbo04[OCBT_RFD1_WB_POS] & (ocbo04[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb2_adr_i);
  wire ocbo03_hazard_d1b2 = ocbo03[OCBT_RFD1_WB_POS] & (ocbo03[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb2_adr_i);
  wire ocbo02_hazard_d1b2 = ocbo02[OCBT_RFD1_WB_POS] & (ocbo02[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb2_adr_i);
  wire ocbo01_hazard_d1b2 = ocbo01[OCBT_RFD1_WB_POS] & (ocbo01[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb2_adr_i);
  // OMAN-to-DECODE hazard D1B2
  wire omn2dec_hazard_d1b2 = dcod_rfb2_req_i &
                             (ocbo07_hazard_d1b2 | ocbo06_hazard_d1b2 | ocbo05_hazard_d1b2 |
                              ocbo04_hazard_d1b2 | ocbo03_hazard_d1b2 | ocbo02_hazard_d1b2 |
                              ocbo01_hazard_d1b2);
  // Reservation station busy D1B2
  wire [DEST_FLAG_ADDR_WIDTH-1:0] hazard_d1b2_ext;
  assign hazard_d1b2_ext = ocbo07_hazard_d1b2 ? ocbo07[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo06_hazard_d1b2 ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo05_hazard_d1b2 ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo04_hazard_d1b2 ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo03_hazard_d1b2 ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo02_hazard_d1b2 ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           ocbo01_hazard_d1b2 ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB];
  assign busy_hazard_d1b2_o     = omn2dec_hazard_d1b2 | exe2dec_hazard_d1b2_o;
  assign busy_hazard_d1b2_adr_o = {hazard_d1b2_ext, dcod_rfb2_adr_i};


  // D2A2
  wire fp64_ocbo07_hazard_d2a2 = fp64_ocbo07[OCBT_RFD2_WB_POS] & (fp64_ocbo07[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa2_adr_i);
  wire fp64_ocbo06_hazard_d2a2 = fp64_ocbo06[OCBT_RFD2_WB_POS] & (fp64_ocbo06[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa2_adr_i);
  wire fp64_ocbo05_hazard_d2a2 = fp64_ocbo05[OCBT_RFD2_WB_POS] & (fp64_ocbo05[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa2_adr_i);
  wire fp64_ocbo04_hazard_d2a2 = fp64_ocbo04[OCBT_RFD2_WB_POS] & (fp64_ocbo04[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa2_adr_i);
  wire fp64_ocbo03_hazard_d2a2 = fp64_ocbo03[OCBT_RFD2_WB_POS] & (fp64_ocbo03[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa2_adr_i);
  wire fp64_ocbo02_hazard_d2a2 = fp64_ocbo02[OCBT_RFD2_WB_POS] & (fp64_ocbo02[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa2_adr_i);
  wire fp64_ocbo01_hazard_d2a2 = fp64_ocbo01[OCBT_RFD2_WB_POS] & (fp64_ocbo01[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa2_adr_i);
  // OMAN-to-DECODE hazard D2A2
  wire omn2dec_hazard_d2a2 = dcod_rfa2_req_i &
                             (fp64_ocbo07_hazard_d2a2 | fp64_ocbo06_hazard_d2a2 | fp64_ocbo05_hazard_d2a2 |
                              fp64_ocbo04_hazard_d2a2 | fp64_ocbo03_hazard_d2a2 | fp64_ocbo02_hazard_d2a2 |
                              fp64_ocbo01_hazard_d2a2);
  // Reservation station busy D2A2
  wire [DEST_FLAG_ADDR_WIDTH-1:0] hazard_d2a2_ext;
  assign hazard_d2a2_ext = fp64_ocbo07_hazard_d2a2 ? ocbo07[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo06_hazard_d2a2 ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo05_hazard_d2a2 ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo04_hazard_d2a2 ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo03_hazard_d2a2 ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo02_hazard_d2a2 ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo01_hazard_d2a2 ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                     ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB];
  assign busy_hazard_d2a2_o     = omn2dec_hazard_d2a2 | exe2dec_hazard_d2a2_o;
  assign busy_hazard_d2a2_adr_o = {hazard_d2a2_ext, dcod_rfa2_adr_i};


  // D2B2
  wire fp64_ocbo07_hazard_d2b2 = fp64_ocbo07[OCBT_RFD2_WB_POS] & (fp64_ocbo07[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb2_adr_i);
  wire fp64_ocbo06_hazard_d2b2 = fp64_ocbo06[OCBT_RFD2_WB_POS] & (fp64_ocbo06[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb2_adr_i);
  wire fp64_ocbo05_hazard_d2b2 = fp64_ocbo05[OCBT_RFD2_WB_POS] & (fp64_ocbo05[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb2_adr_i);
  wire fp64_ocbo04_hazard_d2b2 = fp64_ocbo04[OCBT_RFD2_WB_POS] & (fp64_ocbo04[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb2_adr_i);
  wire fp64_ocbo03_hazard_d2b2 = fp64_ocbo03[OCBT_RFD2_WB_POS] & (fp64_ocbo03[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb2_adr_i);
  wire fp64_ocbo02_hazard_d2b2 = fp64_ocbo02[OCBT_RFD2_WB_POS] & (fp64_ocbo02[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb2_adr_i);
  wire fp64_ocbo01_hazard_d2b2 = fp64_ocbo01[OCBT_RFD2_WB_POS] & (fp64_ocbo01[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb2_adr_i);
  // OMAN-to-DECODE hazard D2B2
  wire omn2dec_hazard_d2b2 = dcod_rfb2_req_i &
                             (fp64_ocbo07_hazard_d2b2 | fp64_ocbo06_hazard_d2b2 | fp64_ocbo05_hazard_d2b2 |
                              fp64_ocbo04_hazard_d2b2 | fp64_ocbo03_hazard_d2b2 | fp64_ocbo02_hazard_d2b2 |
                              fp64_ocbo01_hazard_d2b2);
  // Reservation station busy D2B2
  wire [DEST_FLAG_ADDR_WIDTH-1:0] hazard_d2b2_ext;
  assign hazard_d2b2_ext = fp64_ocbo07_hazard_d2b2 ? ocbo07[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo06_hazard_d2b2 ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo05_hazard_d2b2 ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo04_hazard_d2b2 ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo03_hazard_d2b2 ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo02_hazard_d2b2 ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                           fp64_ocbo01_hazard_d2b2 ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                     ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB];
  assign busy_hazard_d2b2_o     = omn2dec_hazard_d2b2 | exe2dec_hazard_d2b2_o;
  assign busy_hazard_d2b2_adr_o = {hazard_d2b2_ext, dcod_rfb2_adr_i};


  // EXEC-to-DECODE hazards by operands
  assign exe2dec_hazard_d1a1_o = dcod_rfa1_req_i &
                                 ocbo00[OCBT_RFD1_WB_POS] & (ocbo00[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa1_adr_i);
  assign exe2dec_hazard_d1b1_o = dcod_rfb1_req_i &
                                 ocbo00[OCBT_RFD1_WB_POS] & (ocbo00[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb1_adr_i);
  assign exe2dec_hazard_d2a1_o = dcod_rfa1_req_i &
                                 fp64_ocbo00[OCBT_RFD2_WB_POS] & (fp64_ocbo00[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa1_adr_i);
  assign exe2dec_hazard_d2b1_o = dcod_rfb1_req_i &
                                 fp64_ocbo00[OCBT_RFD2_WB_POS] & (fp64_ocbo00[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb1_adr_i);
  assign exe2dec_hazard_d1a2_o = dcod_rfa2_req_i &
                                 ocbo00[OCBT_RFD1_WB_POS] & (ocbo00[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfa2_adr_i);
  assign exe2dec_hazard_d1b2_o = dcod_rfb2_req_i &
                                 ocbo00[OCBT_RFD1_WB_POS] & (ocbo00[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB] == dcod_rfb2_adr_i);
  assign exe2dec_hazard_d2a2_o = dcod_rfa2_req_i &
                                 fp64_ocbo00[OCBT_RFD2_WB_POS] & (fp64_ocbo00[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfa2_adr_i);
  assign exe2dec_hazard_d2b2_o = dcod_rfb2_req_i &
                                 fp64_ocbo00[OCBT_RFD2_WB_POS] & (fp64_ocbo00[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB] == dcod_rfb2_adr_i);



  // OMAN-to-DECODE hazard by FLAG
  wire omn2dec_hazard_f = dcod_flag_req_i &
                          (ocbo07[OCBT_FLAG_WB_POS] | ocbo06[OCBT_FLAG_WB_POS] | ocbo05[OCBT_FLAG_WB_POS] |
                           ocbo04[OCBT_FLAG_WB_POS] | ocbo03[OCBT_FLAG_WB_POS] | ocbo02[OCBT_FLAG_WB_POS] |
                           ocbo01[OCBT_FLAG_WB_POS]);
  // EXEC-to-DECODE hazard by FLAG
  wire exe2dec_hazard_f = dcod_flag_req_i  & ocbo00[OCBT_FLAG_WB_POS];
  // BUSY hazard by FLAG
  assign busy_hazard_f_o     = omn2dec_hazard_f | exe2dec_hazard_f;
  assign busy_hazard_f_adr_o = ocbo07[OCBT_FLAG_WB_POS] ? ocbo07[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                               ocbo06[OCBT_FLAG_WB_POS] ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                               ocbo05[OCBT_FLAG_WB_POS] ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                               ocbo04[OCBT_FLAG_WB_POS] ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                               ocbo03[OCBT_FLAG_WB_POS] ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                               ocbo02[OCBT_FLAG_WB_POS] ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                               ocbo01[OCBT_FLAG_WB_POS] ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                          ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB];


  // OMAN-to-DECODE hazard by CARRY
  wire omn2dec_hazard_c = dcod_carry_req_i &
                          (ocbo07[OCBT_CARRY_WB_POS] | ocbo06[OCBT_CARRY_WB_POS] | ocbo05[OCBT_CARRY_WB_POS] |
                           ocbo04[OCBT_CARRY_WB_POS] | ocbo03[OCBT_CARRY_WB_POS] | ocbo02[OCBT_CARRY_WB_POS] |
                           ocbo01[OCBT_CARRY_WB_POS]);
  // EXEC-to-DECODE hazard by CARRY
  wire exe2dec_hazard_c = dcod_carry_req_i & ocbo00[OCBT_CARRY_WB_POS];
  // BUSY hazard by CARRY
  assign busy_hazard_c_o     = omn2dec_hazard_c | exe2dec_hazard_c;
  assign busy_hazard_c_adr_o = ocbo07[OCBT_CARRY_WB_POS] ? ocbo07[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                               ocbo06[OCBT_CARRY_WB_POS] ? ocbo06[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                               ocbo05[OCBT_CARRY_WB_POS] ? ocbo05[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                               ocbo04[OCBT_CARRY_WB_POS] ? ocbo04[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                               ocbo03[OCBT_CARRY_WB_POS] ? ocbo03[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                               ocbo02[OCBT_CARRY_WB_POS] ? ocbo02[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                               ocbo01[OCBT_CARRY_WB_POS] ? ocbo01[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB] :
                                                           ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB];


  //  OMAN-to-DECODE combined flags
  wire   omn2dec_a_hazard_common = omn2dec_hazard_d2b1 | omn2dec_hazard_d2a1 | omn2dec_hazard_d1b1 | omn2dec_hazard_d1a1;
  assign omn2dec_a_hazard_lsu_o  = omn2dec_a_hazard_common;
  assign omn2dec_a_hazard_1clk_o = omn2dec_hazard_c | omn2dec_hazard_f | omn2dec_a_hazard_common;
  assign omn2dec_a_hazard_mclk_o = omn2dec_hazard_d2b2 | omn2dec_hazard_d2a2 | omn2dec_hazard_d1b2 | omn2dec_hazard_d1a2 | omn2dec_a_hazard_common;


  //  EXEC-to-DECODE combined flags
  wire   exe2dec_a_hazard_common = exe2dec_hazard_d2b1_o | exe2dec_hazard_d2a1_o | exe2dec_hazard_d1b1_o | exe2dec_hazard_d1a1_o;
  assign exe2dec_a_hazard_lsu_o  = exe2dec_a_hazard_common;
  assign exe2dec_a_hazard_1clk_o = exe2dec_a_hazard_common;
  assign exe2dec_a_hazard_mclk_o = exe2dec_hazard_d2b2_o | exe2dec_hazard_d2a2_o | exe2dec_hazard_d1b2_o | exe2dec_hazard_d1a2_o | exe2dec_a_hazard_common;



  // Data for resolving hazards by passing from DECODE to EXECUTE
  //  for FLAG and CARRY
  assign exec_flag_wb_o        = ocbo00[OCBT_FLAG_WB_POS];
  assign exec_carry_wb_o       = ocbo00[OCBT_CARRY_WB_POS];
  assign exec_flag_carry_adr_o = ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB];
  //  for RFD1
  assign exec_rfd1_wb_o  = ocbo00[OCBT_RFD1_WB_POS];
  assign exec_rfd1_adr_o = {ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB],ocbo00[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB]};
  //  for RFD2
  assign exec_rfd2_wb_o  = fp64_ocbo00[OCBT_RFD2_WB_POS];
  assign exec_rfd2_adr_o = {ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB],fp64_ocbo00[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB]};


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
                        (fpxx_arith_valid_i & ocbo00[OCBT_OP_FPXX_ARITH_POS]) |
                        grant_wb_to_fp64_cmp_o |
                        (lsu_valid_i & ocbo00[OCBT_OP_LS_POS]) |
                        ocbo00[OCBT_OP_PASS_EXEC_POS] | // also includes l.rfe in the sense
                        ocbo00[OCBT_FD_AN_EXCEPT_POS];

  // DECODE stall components
  //  stall by unit usage hazard
  //     (unit could be either busy or waiting for WB access)
  wire stall_by_hazard_u =
    (dcod_op_1clk_i & op_1clk_busy_i) |
    ((dcod_op_mul_i | dcod_op_div_i | dcod_op_fpxx_arith_i | dcod_op_fp64_cmp_i) & mclk_busy_i) |
    ((dcod_op_ls_i | dcod_op_msync_i) & lsu_busy_i);

  //  stall by l.jr/l.jalr : MAROCCHINO_TODO
  wire stall_by_jr = dcod_op_jr_i & (omn2dec_hazard_d1b1 | exe2dec_hazard_d1b1_o);

  // stall by l.bf/l.bnf
  // waiting computation of either multi-cycle flag or pending 1-clk flag
  //
  wire ocb_flag_mcycle = ocbo07[OCBT_FLAG_WB_MCYCLE_POS] | ocbo06[OCBT_FLAG_WB_MCYCLE_POS] |
                         ocbo05[OCBT_FLAG_WB_MCYCLE_POS] | ocbo04[OCBT_FLAG_WB_MCYCLE_POS] |
                         ocbo03[OCBT_FLAG_WB_MCYCLE_POS] | ocbo02[OCBT_FLAG_WB_MCYCLE_POS] |
                         ocbo01[OCBT_FLAG_WB_MCYCLE_POS] |
                         ocbo00[OCBT_FLAG_WB_MCYCLE_POS];
  //    MAROCCHINO_TODO: ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  //                     performance improvement is possible with
  //                     forwarding of result of multi-cycle instructions
  //                     like l.swa of float64 comparison.
  wire stall_by_brcond = dcod_op_brcond_i & (busy_op_1clk_cmp_i | ocb_flag_mcycle);

  //  stall by:
  //    a) MF(T)SPR in decode till and OCB become empty (see here)
  //    b) till completion MF(T)SPR (see CTRL)
  //       this completion generates padv-wb,
  //       in next turn padv-wb cleans up OCB and restores
  //       instructions issue
  wire stall_by_mXspr = (dcod_op_mtspr_i | dcod_op_mfspr_i) & ~ocb_empty;

  // combine stalls to decode-valid flag
  assign dcod_valid_o = ~stall_by_hazard_u & ~ocb_full        &
                        ~stall_by_jr       & ~stall_by_brcond &
                        ~stall_by_mXspr;


  // Stall FETCH advancing (see also CTRL) when an l.rfe/ecxeptions are in decode stage.
  // The main purpose of this is waiting till l.rfe/exceptions propagate
  // up to WB stage.
  assign stall_fetch_o = dcod_op_rfe_i | dcod_an_except;

  // Signal to FETCH that target address or flag isn't ready
  assign fetch_waiting_target_o = stall_by_jr | stall_by_brcond;


  // Support IBUS error handling in CTRL
  assign exec_jump_or_branch_o = ocbo00[OCBT_JUMP_OR_BRANCH_POS];
  assign pc_exec_o             = ocbo00[OCBT_PC_MSB:OCBT_PC_LSB];


  //   Flag to enabel/disable exterlal interrupts processing
  // depending on the fact is instructions restartable or not
  assign exec_interrupts_en_o = ocbo00[OCBT_INTERRUPTS_EN_POS];


  // WB-request (1-clock to prevent extra writes in RF)
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      wb_rfd1_wb_o  <= 1'b0;
      wb_flag_wb_o  <= 1'b0;
      wb_carry_wb_o <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      wb_rfd1_wb_o  <= 1'b0;
      wb_flag_wb_o  <= 1'b0;
      wb_carry_wb_o <= 1'b0;
    end
    else if (padv_wb_i) begin
      wb_rfd1_wb_o  <= ocbo00[OCBT_RFD1_WB_POS];
      wb_flag_wb_o  <= ocbo00[OCBT_FLAG_WB_POS];
      wb_carry_wb_o <= ocbo00[OCBT_CARRY_WB_POS];
    end
    else begin
      wb_rfd1_wb_o  <= 1'b0;
      wb_flag_wb_o  <= 1'b0;
      wb_carry_wb_o <= 1'b0;
    end
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
      wb_flag_carry_adr_o <=  ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB];
      wb_rfd1_adr_o       <= {ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB],ocbo00[OCBT_RFD1_ADR_MSB:OCBT_RFD1_ADR_LSB]};
      pc_wb_o             <= ocbo00[OCBT_PC_MSB:OCBT_PC_LSB];
    end
  end // @clock

  // for FPU64
  // 1-clock write back pulse for low bits of D
  reg wb_rfd2_wb_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_rfd2_wb_r <= 1'b0;
    else if (pipeline_flush_i)
      wb_rfd2_wb_r <= 1'b0;
    else if (padv_wb_i)
      wb_rfd2_wb_r <= fp64_ocbo00[OCBT_RFD2_WB_POS];
    else
      wb_rfd2_wb_r <= 1'b0;
  end // @clock
  // destination address for low bits
  reg [DEST_REG_ADDR_WIDTH-1:0] wb_rfd2_adr_r;
  // ---
  always @(posedge clk) begin
    if (padv_wb_i & ~pipeline_flush_i)
      wb_rfd2_adr_r <= {ocbo00[OCBT_EXT_ADR_MSB:OCBT_EXT_ADR_LSB],fp64_ocbo00[OCBT_RFD2_ADR_MSB:OCBT_RFD2_ADR_LSB]};
  end // @clock
  // output assignement
  assign wb_rfd2_wb_o  = wb_rfd2_wb_r;
  assign wb_rfd2_adr_o = wb_rfd2_adr_r;


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
