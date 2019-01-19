/////////////////////////////////////////////////////////////////////
//                                                                 //
//  mor1kx_oman_marocchino                                         //
//                                                                 //
//  Description: mor1kx [O]rder [MAN]ager unit                     //
//               for MAROCCHINO pipeline                           //
//    a) collect various state signals from DECODE                 //
//       and EXECUTE modules                                       //
//    b) analisys of conflicts                                     //
//    c) generate valid flags for advance DECODE and Write-Back    //
//                                                                 //
/////////////////////////////////////////////////////////////////////
//                                                                 //
//   Copyright (C) 2015-2018 Andrey Bacherov                       //
//                      avbacherov@opencores.org                   //
//                                                                 //
//      This Source Code Form is subject to the terms of the       //
//      Open Hardware Description License, v. 1.0. If a copy       //
//      of the OHDL was not distributed with this file, You        //
//      can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt    //
//                                                                 //
/////////////////////////////////////////////////////////////////////

`include "mor1kx-defines.v"



/////////////////////////////////////////////////////////////////////
//  Single cell of [R]egisters [A]llocation [T]able                //
/////////////////////////////////////////////////////////////////////

module rat_cell
#(
  parameter OPTION_RF_ADDR_WIDTH =  5,
  parameter DEST_EXTADR_WIDTH    =  3,
  parameter GPR_ADDR             =  0
)
(
  // clock & reset
  input                                 cpu_clk,

  // pipeline control
  input                                 padv_exec_i,
  input                                 padv_wrbk_i,
  input                                 pipeline_flush_i,

  // input allocation information
  //  # allocated as D1
  input                                 dcod_rfd1_we_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfd1_adr_i,
  //  # allocated as D2
  input                                 dcod_rfd2_we_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfd2_adr_i,
  //  # allocation id
  input         [DEST_EXTADR_WIDTH-1:0] dcod_extadr_i,

  // input to clear allocation bits
  input         [DEST_EXTADR_WIDTH-1:0] exec_extadr_i,

  // output allocation information
  output reg                            rat_rd1_alloc_o,      // allocated by D1
  output reg                            rat_rd2_alloc_o,      // allocated by D2
  output reg    [DEST_EXTADR_WIDTH-1:0] rat_extadr_o          // allocation ID
);

  localparam [OPTION_RF_ADDR_WIDTH-1:0] GPR_ADR = GPR_ADDR;

  // set allocation flags
  wire set_rd1_alloc = dcod_rfd1_we_i & (dcod_rfd1_adr_i == GPR_ADR);
  wire set_rd2_alloc = dcod_rfd2_we_i & (dcod_rfd2_adr_i == GPR_ADR);
  wire set_rdx_alloc = (set_rd1_alloc | set_rd2_alloc);

  // condition to keep allocation flags at write-back
  wire rat_alloc_at_wrbk     = (rat_extadr_o != exec_extadr_i);
  // next values of allocation flags at write-back
  wire rat_rd1_alloc_at_wrbk = rat_rd1_alloc_o & rat_alloc_at_wrbk;
  wire rat_rd2_alloc_at_wrbk = rat_rd2_alloc_o & rat_alloc_at_wrbk;

  // allocation flags
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i) begin
      rat_rd1_alloc_o <= 1'b0;
      rat_rd2_alloc_o <= 1'b0;
    end
    else begin
      case ({padv_wrbk_i, padv_exec_i})
        // keep state
        2'b00: begin
        end
        // advance EXECUTE only
        2'b01: begin
          rat_rd1_alloc_o <= set_rdx_alloc ? set_rd1_alloc : rat_rd1_alloc_o;
          rat_rd2_alloc_o <= set_rdx_alloc ? set_rd2_alloc : rat_rd2_alloc_o;
        end
        // advance WriteBack only
        2'b10: begin
          rat_rd1_alloc_o <= rat_rd1_alloc_at_wrbk;
          rat_rd2_alloc_o <= rat_rd2_alloc_at_wrbk;
        end
        // advance EXECUTE and WriteBack simultaneously
        2'b11: begin
          rat_rd1_alloc_o <= set_rdx_alloc ? set_rd1_alloc : rat_rd1_alloc_at_wrbk;
          rat_rd2_alloc_o <= set_rdx_alloc ? set_rd2_alloc : rat_rd2_alloc_at_wrbk;
        end
      endcase
    end // regular update
  end // at clock

  // extention bits
  always @(posedge cpu_clk) begin
    if (padv_exec_i)
      rat_extadr_o <= set_rdx_alloc ? dcod_extadr_i : rat_extadr_o;
  end

endmodule // rat_cell



/////////////////////////////////////////////////////////////////////
//  [O]rder [MAN]ager itself                                       //
/////////////////////////////////////////////////////////////////////

module mor1kx_oman_marocchino
#(
  parameter OPTION_OPERAND_WIDTH = 32,
  parameter OPTION_RF_ADDR_WIDTH =  5,
  parameter NUM_GPRS             = 32,  // (1 << OPTION_RF_ADDR_WIDTH)
  parameter DEST_EXTADR_WIDTH    =  3,  // log2(Order Control Buffer depth)
  // branch predictor parameters
  parameter GSHARE_BITS_NUM      = 10
)
(
  // clock & reset
  input                                 cpu_clk,
  input                                 cpu_rst,

  // pipeline control
  input                                 padv_dcod_i,
  input                                 padv_exec_i,
  input                                 padv_wrbk_i,
  input                                 pipeline_flush_i,

  // fetched instruction is valid
  input                                 fetch_valid_i,
  input                                 fetch_delay_slot_i,

  // for l.jr/l.jalr processing
  input      [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfb1_adr_i,

  // DECODE flags to indicate next required unit
  // (The information is stored in order control buffer)
  input                                 dcod_op_push_wrbk_i,
  input                                 fetch_op_jb_i,
  input                                 dcod_op_div_i,
  input                                 dcod_op_mul_i,
  input                                 dcod_op_fpxx_arith_i,
  input                                 dcod_op_ls_i,     // load / store (we need store for pushing LSU exceptions)
  input                                 dcod_op_rfe_i,    // l.rfe
  // for FPU3264
  input                                 dcod_op_fpxx_cmp_i,

  // DECODE additional information related instruction
  //  part #1: information stored in order control buffer
  input      [OPTION_OPERAND_WIDTH-1:0] pc_decode_i,            // instruction virtual address
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfd1_adr_i,        // Write-Back address
  input                                 dcod_rfd1_we_i,         // instruction generates Write-Back to D1
  input                                 dcod_flag_we_i,         // any instruction which affects comparison flag
  input                                 dcod_delay_slot_i,      // instruction is in delay slot
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfd2_adr_i,        // Write-Back address for FPU64
  input                                 dcod_rfd2_we_i,         // instruction generates Write-Back to D2
  //  part #2: information required for create enable for
  //           for external (timer/ethernet/uart/etc) interrupts
  input                                 dcod_op_lsu_store_i,
  input                                 dcod_op_msync_i,
  input                                 dcod_op_mXspr_i,

  // for unit hazard detection
  input                                 dcod_op_1clk_i,

  // collect valid flags from execution modules
  input                                 op_1clk_valid_i,
  input                                 div_valid_i,
  input                                 mul_valid_i,
  input                                 fpxx_arith_valid_i,
  input                                 fpxx_cmp_valid_i,
  input                                 lsu_valid_i,

  // FETCH & DECODE exceptions
  input                                 fetch_except_ibus_err_i,
  input                                 fetch_except_ipagefault_i,
  input                                 fetch_except_itlb_miss_i,
  input                                 dcod_except_illegal_i,
  input                                 dcod_except_syscall_i,
  input                                 dcod_except_trap_i,
  input                                 dcod_an_except_fd_i,

  // OMAN-to-DECODE hazards
  //  # relative operand A1
  input                                 dcod_rfa1_req_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa1_adr_i,
  output                                omn2dec_hazard_d1a1_o,
  output                                omn2dec_hazard_d2a1_o,
  output        [DEST_EXTADR_WIDTH-1:0] omn2dec_extadr_dxa1_o,
  //  # relative operand B1
  input                                 dcod_rfb1_req_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb1_adr_i,
  output                                omn2dec_hazard_d1b1_o,
  output                                omn2dec_hazard_d2b1_o,
  output        [DEST_EXTADR_WIDTH-1:0] omn2dec_extadr_dxb1_o,
  //  # relative operand A2
  input                                 dcod_rfa2_req_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa2_adr_i,
  output                                omn2dec_hazard_d1a2_o,
  output                                omn2dec_hazard_d2a2_o,
  output        [DEST_EXTADR_WIDTH-1:0] omn2dec_extadr_dxa2_o,
  //  # relative operand B2
  input                                 dcod_rfb2_req_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb2_adr_i,
  output                                omn2dec_hazard_d1b2_o,
  output                                omn2dec_hazard_d2b2_o,
  output        [DEST_EXTADR_WIDTH-1:0] omn2dec_extadr_dxb2_o,

  // support in-1clk-unit forwarding
  output        [DEST_EXTADR_WIDTH-1:0] dcod_extadr_o,

  // [O]rder [C]ontrol [B]uffer statuses
  output                                ocb_full_o,
  output                                ocb_empty_o,

  // DECODE result could be processed by EXECUTE
  output                                dcod_free_o,

  // EXECUTE completed (desired unit is ready)
  output                                exec_valid_o,

  // control Write-Back latches of execution modules
  output                                grant_wrbk_to_1clk_o,
  output                                grant_wrbk_to_div_o,
  output                                grant_wrbk_to_mul_o,
  output                                grant_wrbk_to_fpxx_arith_o,
  output                                grant_wrbk_to_lsu_o,
  // for FPU64
  output                                grant_wrbk_to_fpxx_cmp_o,

  // Logic to support Jump / Branch taking
  //  # from IFETCH
  //    ## jump/branch variants
  input                                 fetch_op_jimm_i,
  input                                 fetch_op_jr_i,
  input                                 fetch_op_bf_i,
  input                                 fetch_op_bnf_i,
  //    ## "to immediate driven target"
  input      [OPTION_OPERAND_WIDTH-1:0] fetch_to_imm_target_i,
  //  # target for l.jr / l.jalr
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_rfb1_jr_i,
  input      [OPTION_OPERAND_WIDTH-1:0] wrbk_result1_i,
  // comparision flag for l.bf/l.bnf
  input                                 ctrl_flag_sr_i,
  // jump/branch signals to IFETCH
  output                                do_branch_o,
  output     [OPTION_OPERAND_WIDTH-1:0] do_branch_target_o,
  output                                jr_gathering_target_o,
  //  # branch prediction support
  input      [OPTION_OPERAND_WIDTH-1:0] after_ds_target_i,
  output                                predict_miss_o,
  input                           [1:0] bc_cnt_value_i,  // current value of saturation counter
  input           [GSHARE_BITS_NUM-1:0] bc_cnt_radr_i,   // saturation counter ID
  output reg                            bc_cnt_we_o,     // update saturation counter
  output reg                      [1:0] bc_cnt_wdat_o,   // new saturation counter value
  output reg      [GSHARE_BITS_NUM-1:0] bc_cnt_wadr_o,   // saturation counter id
  output reg                            bc_hist_taken_o, // conditional branch really taken
  // Support IBUS error handling in CTRL
  output reg                            wrbk_jump_or_branch_o,
  output reg                            wrbk_jump_o,
  output reg                            wrbk_op_bf_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] wrbk_jb_target_o,


  //   Flag to enabel/disable exterlal interrupts processing
  // depending on the fact is instructions restartable or not
  output                                exec_interrupts_en_o,

  // pre-Write-Back l.rfe
  output                                exec_op_rfe_o,
  // pre-Write-Back output exceptions: IFETCH
  output                                exec_except_ibus_err_o,
  output                                exec_except_ipagefault_o,
  output                                exec_except_itlb_miss_o,
  output                                exec_except_ibus_align_o,
  // pre-Write-Back output exceptions: DECODE
  output                                exec_except_illegal_o,
  output                                exec_except_syscall_o,
  output                                exec_except_trap_o,
  // pre-Write-Back output exceptions: IFETCH/DECODE
  output                                exec_an_except_fd_o,

  // Write-Back outputs
  //  ## special Write-Back-controls for RF
  output reg             [NUM_GPRS-1:0] wrbk_rfd1_we1h_o,
  output reg                            wrbk_rfd1_we_o,
  output reg [OPTION_RF_ADDR_WIDTH-1:0] wrbk_rfd1_adr_o,
  output reg             [NUM_GPRS-1:0] wrbk_rfd2_we1h_o,
  output reg                            wrbk_rfd2_we_o,
  output reg [OPTION_RF_ADDR_WIDTH-1:0] wrbk_rfd2_adr_o,
  //  ## instruction related information
  output reg [OPTION_OPERAND_WIDTH-1:0] pc_wrbk_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] pc_nxt_wrbk_o, // pc-wrbk + 4
  output reg [OPTION_OPERAND_WIDTH-1:0] pc_nxt2_wrbk_o, // pc-wrbk + 8
  output reg                            wrbk_delay_slot_o,
  // for hazards resolution in RSRVS
  output reg    [DEST_EXTADR_WIDTH-1:0] wrbk_extadr_o
);

  // [O]rder [C]ontrol [B]uffer [T]ap layout
  //  --- [A]ttributes ---
  //  [0...5] Exceptions generated by FETCH & DECODE.
  //    (a) Doesn't include IBUS align violation.
  //        It goes through "jump/branch attributes order control buffer".
  //    (b) LSU exceptions go to Write-Back around any OCB
  //  [6] Combined IFETCH/DECODE an exception flag
  localparam  OCBTA_AN_EXCEPT_FD_POS   =                           6;
  //  Flag that external interrupt is enabled (instruction is re-startable)
  localparam  OCBTA_INTERRUPTS_EN_POS  = OCBTA_AN_EXCEPT_FD_POS  + 1;
  //  Unit wise requested/ready
  localparam  OCBTA_OP_RFE_POS         = OCBTA_INTERRUPTS_EN_POS + 1;
  //  Instruction is in delay slot
  localparam  OCBTA_DELAY_SLOT_POS     = OCBTA_OP_RFE_POS        + 1;
  //  Instruction generates Write-Back to D1
  localparam  OCBTA_RFD1_WRBK_POS      = OCBTA_DELAY_SLOT_POS    + 1;
  localparam  OCBTA_RFD1_ADR_LSB       = OCBTA_RFD1_WRBK_POS     + 1;
  localparam  OCBTA_RFD1_ADR_MSB       = OCBTA_RFD1_WRBK_POS     + OPTION_RF_ADDR_WIDTH;
  //  Instruction generates Write-Back to D2
  localparam  OCBTA_RFD2_WRBK_POS      = OCBTA_RFD1_ADR_MSB      + 1;
  localparam  OCBTA_RFD2_ADR_LSB       = OCBTA_RFD2_WRBK_POS     + 1;
  localparam  OCBTA_RFD2_ADR_MSB       = OCBTA_RFD2_WRBK_POS     + OPTION_RF_ADDR_WIDTH;
  //  Program counter
  localparam  OCBTA_PC_LSB             = OCBTA_RFD2_ADR_MSB      + 1;
  localparam  OCBTA_PC_MSB             = OCBTA_RFD2_ADR_MSB      + OPTION_OPERAND_WIDTH;
  // --- pipeline [C]ontrol flags ---
  localparam  OCBTC_OP_PUSH_WRBK_POS   = OCBTA_PC_MSB             + 1;
  localparam  OCBTC_JUMP_OR_BRANCH_POS = OCBTC_OP_PUSH_WRBK_POS   + 1;
  localparam  OCBTC_OP_1CLK_POS        = OCBTC_JUMP_OR_BRANCH_POS + 1;
  localparam  OCBTC_OP_DIV_POS         = OCBTC_OP_1CLK_POS        + 1;
  localparam  OCBTC_OP_MUL_POS         = OCBTC_OP_DIV_POS         + 1;
  localparam  OCBTC_OP_FPXX_ARITH_POS  = OCBTC_OP_MUL_POS         + 1; // arithmetic part only
  localparam  OCBTC_OP_FPXX_CMP_POS    = OCBTC_OP_FPXX_ARITH_POS  + 1; // granting write back to fpxx comparison
  localparam  OCBTC_OP_LS_POS          = OCBTC_OP_FPXX_CMP_POS    + 1; // load / store
  // we also reset extention bits because zero value is meaningfull
  localparam  OCBTC_EXTADR_LSB         = OCBTC_OP_LS_POS          + 1;
  localparam  OCBTC_EXTADR_MSB         = OCBTC_OP_LS_POS          + DEST_EXTADR_WIDTH;
  // value of MSB of order control buffer tap
  localparam  OCBT_MSB                 = OCBTC_EXTADR_MSB;
  localparam  OCBT_WIDTH               = OCBT_MSB                 + 1;


  // a jump/branch instruction in DECODE
  reg dcod_op_jb_r;
  // ---
  always @(posedge cpu_clk) begin
    if (padv_dcod_i)
      dcod_op_jb_r <= fetch_op_jb_i;
  end // at clock

  // IFETCH exceptions in DECODE
  reg dcod_fetch_except_ibus_err_r;
  reg dcod_fetch_except_ipagefault_r;
  reg dcod_fetch_except_itlb_miss_r;
  // ---
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i) begin
      dcod_fetch_except_ibus_err_r   <= 1'b0;
      dcod_fetch_except_ipagefault_r <= 1'b0;
      dcod_fetch_except_itlb_miss_r  <= 1'b0;
    end
    else if (padv_dcod_i) begin
      dcod_fetch_except_ibus_err_r   <= fetch_except_ibus_err_i;
      dcod_fetch_except_ipagefault_r <= fetch_except_ipagefault_i;
      dcod_fetch_except_itlb_miss_r  <= fetch_except_itlb_miss_i;
    end
    else if (padv_exec_i) begin
      dcod_fetch_except_ibus_err_r   <= 1'b0;
      dcod_fetch_except_ipagefault_r <= 1'b0;
      dcod_fetch_except_itlb_miss_r  <= 1'b0;
    end
  end // at clock


  // extension to DEST, FLAG or CARRY
  // Zero value is reserved as "not used"
  localparam [DEST_EXTADR_WIDTH-1:0] EXTADR_MAX = ((1 << DEST_EXTADR_WIDTH) - 1);
  localparam [DEST_EXTADR_WIDTH-1:0] EXTADR_MIN = 1;
  // ---
  reg  [DEST_EXTADR_WIDTH-1:0] dcod_extadr_r;
  wire [DEST_EXTADR_WIDTH-1:0] extadr_adder;
  // ---
  assign extadr_adder = (dcod_extadr_r == EXTADR_MAX) ? EXTADR_MIN : (dcod_extadr_r + 1'b1);
  // ---
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      dcod_extadr_r <= {DEST_EXTADR_WIDTH{1'b0}};
    else if (padv_dcod_i)
      dcod_extadr_r <= fetch_valid_i ? extadr_adder : dcod_extadr_r;
  end // @clock
  // support in-1clk-unit forwarding
  assign dcod_extadr_o = dcod_extadr_r;


  // Flag that istruction is restrartable.
  // Instructions which are not restartable:
  //     "store" - they are buffered and couldn't be removed from buffer
  //               till execution completion
  //     l.msync - it forces LSU to report "busy" till completion of
  //               all previously issued loads and stores
  //     l.mtspr - change internal CPU control registers
  //     l.mfspr - combined with l.mtspr (_mXspr_) to reduce combinatorial logic
  //     l.rfe   - cause return from exception process with serious
  //               changing CPU state.
  //   Note #1 we just not run execution for "invalid" command (CTRL), so
  // such "commands" don't achieve Write-Back where exceptions are processed.
  //   Note #2 l.rfe is a special case. We push pipe full of rfes.
  // The reason for this is that we need the rfe to reach Write-Back stage
  // so it will cause the branch. It will clear itself by the
  // pipeline_flush_i that the rfe will generate.
  wire interrupts_en = ~(dcod_op_lsu_store_i | dcod_op_msync_i | dcod_op_mXspr_i | dcod_op_rfe_i);


  // Compute OCBs depth
  localparam INSN_OCB_NUM_TAPS    = EXTADR_MAX - 1; // extention bits "0" is reserved as "not used"
  localparam JB_ATTR_OCB_NUM_TAPS = (INSN_OCB_NUM_TAPS >> 1) + 1;


  //-------------------//
  // INSN OCB instance //
  //-------------------//

  // --- OCB-Controls input ---
  wire  [OCBT_MSB:0] ocbi;
  assign ocbi =
    {
      // --- pipeline [C]ontrol flags ---
      dcod_extadr_r, // OCB-Controls entrance
      dcod_op_ls_i, // OCB-Controls entrance
      dcod_op_fpxx_cmp_i, // OCB-Controls entrance
      dcod_op_fpxx_arith_i, // OCB-Controls entrance
      dcod_op_mul_i, // OCB-Controls entrance
      dcod_op_div_i, // OCB-Controls entrance
      dcod_op_1clk_i, // OCB-Controls entrance
      dcod_op_jb_r, // OCB-Controls entrance
      dcod_op_push_wrbk_i, // OCB-Controls entrance
      // --- instruction [A]ttributes ---
      pc_decode_i, // OCB-Attributes entrance
      dcod_rfd2_adr_i, // OCB-Attributes entrance
      dcod_rfd2_we_i, // OCB-Attributes entrance
      dcod_rfd1_adr_i, // OCB-Attributes entrance
      dcod_rfd1_we_i, // OCB-Attributes entrance
      dcod_delay_slot_i, // OCB-Attributes entrance
      dcod_op_rfe_i, // OCB-Attributes entrance
      // Flag that istruction is restartable
      interrupts_en, // OCB-Attributes entrance
      // Combined IFETCH/DECODE an exception flag
      dcod_an_except_fd_i, // OCB-Attributes entrance
      // FETCH & DECODE exceptions
      dcod_fetch_except_ibus_err_r, // OCB-Attributes entrance
      dcod_fetch_except_ipagefault_r, // OCB-Attributes entrance
      dcod_fetch_except_itlb_miss_r, // OCB-Attributes entrance
      dcod_except_illegal_i, // OCB-Attributes entrance
      dcod_except_syscall_i, // OCB-Attributes entrance
      dcod_except_trap_i // OCB-Attributes entrance
    };

  // --- INSN OCB input ---
  wire [OCBT_MSB:0] ocbo;

  // --- INSN OCB instance ---
  mor1kx_ff_oreg_buff_marocchino
  #(
    .NUM_TAPS         (INSN_OCB_NUM_TAPS), // INSN_OCB
    .DATA_WIDTH       (OCBT_WIDTH), // INSN_OCB
    .FULL_FLAG        ("ENABLED"), // INSN_OCB
    .EMPTY_FLAG       ("ENABLED") // INSN_OCB
  )
  u_ocb
  (
    // clocks, resets
    .cpu_clk          (cpu_clk), // INSN_OCB
    // resets
    .ini_rst          (pipeline_flush_i), // JB-ATTR-OCB
    .ext_rst          (1'b0), // JB-ATTR-OCB
    // RW-controls
    .write_i          (padv_exec_i), // INSN_OCB
    .read_i           (padv_wrbk_i), // INSN_OCB
    // data input
    .data_i           (ocbi), // INSN_OCB
    // "OCB is empty" flag
    .empty_o          (ocb_empty_o), // INSN_OCB
    // "OCB is full" flag
    .full_o           (ocb_full_o), // INSN_OCB
    // output register
    .data_o           (ocbo) // INSN_OCB
  );


  // Grant Write-Back-access to units
  assign grant_wrbk_to_1clk_o        = ocbo[OCBTC_OP_1CLK_POS];
  assign grant_wrbk_to_div_o         = ocbo[OCBTC_OP_DIV_POS];
  assign grant_wrbk_to_mul_o         = ocbo[OCBTC_OP_MUL_POS];
  assign grant_wrbk_to_fpxx_arith_o  = ocbo[OCBTC_OP_FPXX_ARITH_POS];
  assign grant_wrbk_to_lsu_o         = ocbo[OCBTC_OP_LS_POS];
  assign grant_wrbk_to_fpxx_cmp_o    = ocbo[OCBTC_OP_FPXX_CMP_POS];


  //--------------------------//
  // Analysis of data hazards //
  //--------------------------//

  // We needn't Write-Back-to-DECODE hazards for FLAG and CARRY:
  //  (a) we process FLAG for l.bf/.bnf in separate way
  //  (b) only 1-clock instructions request FLAG/CARRY,
  //      however any case they granted with Write-Back accees after completion FLAG/CARRY update

  // Extention bits visible at EXECUTE output
  wire [(DEST_EXTADR_WIDTH-1):0] exec_extadr = ocbo[OCBTC_EXTADR_MSB:OCBTC_EXTADR_LSB];

  // RAT outputs
  wire          [(NUM_GPRS-1):0] rat_rd1_alloc; // allocated by D1
  wire          [(NUM_GPRS-1):0] rat_rd2_alloc; // allocated by D2
  wire [(DEST_EXTADR_WIDTH-1):0] rat_extadr [(NUM_GPRS-1):0]; // allocation ID

  // Special case for GPR[0]
  assign rat_rd1_alloc[0] = 1'b0;
  assign rat_rd2_alloc[0] = 1'b0;
  assign rat_extadr[0]    = {DEST_EXTADR_WIDTH{1'b0}};

  // instances for RAT cells
  generate
  genvar ic;
  for (ic = 1; ic < NUM_GPRS; ic = ic + 1) begin : rat_cell_k
    // RAT cells instansence
    rat_cell
    #(
      .OPTION_RF_ADDR_WIDTH   (OPTION_RF_ADDR_WIDTH), // RAT-CELL
      .DEST_EXTADR_WIDTH      (DEST_EXTADR_WIDTH), // RAT-CELL
      .GPR_ADDR               (ic) // RAT-CELL
    )
    u_rat_cell
    (
      // clock & reset
      .cpu_clk                (cpu_clk), // RAT-CELL
      // pipeline control
      .padv_exec_i            (padv_exec_i), // RAT-CELL
      .padv_wrbk_i            (padv_wrbk_i), // RAT-CELL
      .pipeline_flush_i       (pipeline_flush_i), // RAT-CELL
      // input allocation information
      //  # allocated as D1
      .dcod_rfd1_we_i         (dcod_rfd1_we_i), // RAT-CELL
      .dcod_rfd1_adr_i        (dcod_rfd1_adr_i), // RAT-CELL
      //  # allocated as D2
      .dcod_rfd2_we_i         (dcod_rfd2_we_i), // RAT-CELL
      .dcod_rfd2_adr_i        (dcod_rfd2_adr_i), // RAT-CELL
      //  # allocation id
      .dcod_extadr_i          (dcod_extadr_r), // RAT-CELL
      // input to clear allocation bits
      .exec_extadr_i          (exec_extadr), // RAT-CELL
      // output allocation information
      .rat_rd1_alloc_o        (rat_rd1_alloc[ic]), // RAT-CELL
      .rat_rd2_alloc_o        (rat_rd2_alloc[ic]), // RAT-CELL
      .rat_extadr_o           (rat_extadr[ic]) // RAT-CELL
    );
  end
  endgenerate


  //----------------------------------//
  // OMAN-to-DECODE hazards for RSRVS //
  //----------------------------------//

  //  # relative operand A1
  assign omn2dec_hazard_d1a1_o = rat_rd1_alloc[dcod_rfa1_adr_i] & dcod_rfa1_req_i;
  assign omn2dec_hazard_d2a1_o = rat_rd2_alloc[dcod_rfa1_adr_i] & dcod_rfa1_req_i;
  assign omn2dec_extadr_dxa1_o = rat_extadr[dcod_rfa1_adr_i];
  //  # relative operand B1
  assign omn2dec_hazard_d1b1_o = rat_rd1_alloc[dcod_rfb1_adr_i] & dcod_rfb1_req_i;
  assign omn2dec_hazard_d2b1_o = rat_rd2_alloc[dcod_rfb1_adr_i] & dcod_rfb1_req_i;
  assign omn2dec_extadr_dxb1_o = rat_extadr[dcod_rfb1_adr_i];
  //  # relative operand A2
  assign omn2dec_hazard_d1a2_o = rat_rd1_alloc[dcod_rfa2_adr_i] & dcod_rfa2_req_i;
  assign omn2dec_hazard_d2a2_o = rat_rd2_alloc[dcod_rfa2_adr_i] & dcod_rfa2_req_i;
  assign omn2dec_extadr_dxa2_o = rat_extadr[dcod_rfa2_adr_i];
  //  # relative operand B2
  assign omn2dec_hazard_d1b2_o = rat_rd1_alloc[dcod_rfb2_adr_i] & dcod_rfb2_req_i;
  assign omn2dec_hazard_d2b2_o = rat_rd2_alloc[dcod_rfb2_adr_i] & dcod_rfb2_req_i;
  assign omn2dec_extadr_dxb2_o = rat_extadr[dcod_rfb2_adr_i];


  //   An execute module is ready and granted access to Write-Back
  //   Instructions l.mf(t)spr have got guaranted Write-Back access because
  // no any new instruction is issued into execution till
  // l.mf(t)spr has been completed. Pay attention that we start
  // l.mf(t)spr ecxecution after completion of all peviously
  // issued instructions only.
  //   l.rfe and FETCH/DECODE exceptions are also should
  // push Write-Back latches
  // ---
  wire   op_1clk_valid_l = op_1clk_valid_i & ocbo[OCBTC_OP_1CLK_POS];
  // ---
  //   Declaration valid flag for jump/branch attributes
  //   For l.jal/l.jalr we use adder in 1-clk to compure return address,
  // so for the cases we additionally wait "jump/branch attributes".
  wire   exec_jb_attr_valid;
  // ---
  assign exec_valid_o =
    (op_1clk_valid_l          & ~ocbo[OCBTC_JUMP_OR_BRANCH_POS]) | // EXEC VALID: but wait attributes for l.jal/ljalr
    (exec_jb_attr_valid       &  ocbo[OCBTC_JUMP_OR_BRANCH_POS]) | // EXEC VALID
    (div_valid_i              &  ocbo[OCBTC_OP_DIV_POS])         | // EXEC VALID
    (mul_valid_i              &  ocbo[OCBTC_OP_MUL_POS])         | // EXEC VALID
    (fpxx_arith_valid_i       &  ocbo[OCBTC_OP_FPXX_ARITH_POS])  | // EXEC VALID
    (fpxx_cmp_valid_i         &  ocbo[OCBTC_OP_FPXX_CMP_POS])    | // EXEC VALID
    (lsu_valid_i              &  ocbo[OCBTC_OP_LS_POS])          | // EXEC VALID
                                 ocbo[OCBTC_OP_PUSH_WRBK_POS];     // EXEC VALID


  //-----------------------------//
  // Taking Jump by Register FSM //
  //-----------------------------//

  // --- various pendings till rB/flag computationcompletion ---
  wire                            jr_dcd2fth_hazard_d1b1_raw; // used only inside J/B FSM
  wire    [DEST_EXTADR_WIDTH-1:0] jr_hazard_ext_raw;
  reg     [DEST_EXTADR_WIDTH-1:0] jb_hazard_ext_p;
  reg  [OPTION_OPERAND_WIDTH-1:0] jr_target_p;
  reg                             jr_gathering_target_p;
  // ---
  assign jr_dcd2fth_hazard_d1b1_raw = (dcod_rfd1_adr_i == fetch_rfb1_adr_i) & dcod_rfd1_we_i;
  assign jr_hazard_ext_raw = rat_extadr[fetch_rfb1_adr_i];

  localparam [3:0] JR_FSM_CATCHING_JR = 4'b0001, // on IFETCH output
                   JR_FSM_GET_B1      = 4'b0010, // get rB for l.jr/ljalr if no hazard
                   JR_FSM_WAITING_B1  = 4'b0100, // waiting rB for l.jr/ljalr if hazard
                   JR_FSM_DOING_JR    = 4'b1000; // execute l.jr/ljalr

  reg [3:0] jr_fsm_state_r;

  wire jr_fsm_catching_jr      = jr_fsm_state_r[0];
  wire jr_fsm_get_b1_state     = jr_fsm_state_r[1];
  wire jr_fsm_waiting_b1_state = jr_fsm_state_r[2];
  wire jr_fsm_doing_jr_state   = jr_fsm_state_r[3];

  always @(posedge cpu_clk) begin
    if (pipeline_flush_i) begin
      jr_fsm_state_r        <= JR_FSM_CATCHING_JR;
      jr_gathering_target_p <= 1'b0;
    end
    else begin
      // synthesis parallel_case
      case (jr_fsm_state_r)
        // catching j/b on IFETCH output
        JR_FSM_CATCHING_JR: begin
          if (padv_dcod_i) begin
            if (fetch_op_jr_i) begin
              jr_gathering_target_p <= 1'b1;
              if (jr_dcd2fth_hazard_d1b1_raw |
                  (rat_rd1_alloc[fetch_rfb1_adr_i] &
                   (wrbk_extadr_o != jr_hazard_ext_raw)))
                jr_fsm_state_r <= JR_FSM_WAITING_B1;
              else
                jr_fsm_state_r <= JR_FSM_GET_B1;
            end
          end
        end

        // gathering target for l.jr/l.jalr
        JR_FSM_GET_B1: begin
          jr_fsm_state_r        <= JR_FSM_DOING_JR;
          jr_gathering_target_p <= 1'b0;
        end
        // waiting target for l.jr/l.jalr
        JR_FSM_WAITING_B1: begin
          if (jb_hazard_ext_p == wrbk_extadr_o) begin
            jr_fsm_state_r        <= JR_FSM_DOING_JR;
            jr_gathering_target_p <= 1'b0;
          end
        end
        // doing l.jr/l.jalr
        JR_FSM_DOING_JR: begin
          jr_fsm_state_r <= JR_FSM_CATCHING_JR;
        end

        // others
        default:;
      endcase
    end
  end // @cpu-clock


  //--------------------------------//
  // Tacking conditional branch FSM //
  //--------------------------------//

  // state machine for tracking Jump / Branch related hazards
  localparam [4:0] BC_FSM_CATCHING_BC           = 5'b00001, // on IFETCH output
                   BC_FSM_DO_INSTANT_BRANCH     = 5'b00010,
                   BC_FSM_PREDICT_CATCHING_DS   = 5'b00100, // from conditional branch till delay slot
                   BC_FSM_PREDICT_WAITING_FLAG  = 5'b01000, // from delay slot till periction reslolving
                   BC_FSM_PREDICT_MISS          = 5'b10000; // restart IFETCH from mispredict target (1-clock)

  reg [4:0] bc_fsm_state_r;

  wire bc_fsm_catching_bc                = bc_fsm_state_r[0];
  wire bc_fsm_do_instant_branch_state    = bc_fsm_state_r[1];
  wire bc_fsm_predict_catching_ds_state  = bc_fsm_state_r[2];
  wire bc_fsm_predict_waiting_flag_state = bc_fsm_state_r[3];
  wire bc_fsm_predict_miss_state         = bc_fsm_state_r[4];


  // --- detect flag hazard for l.bf/l.bnf ---
  wire                         flag_alloc_w;
  reg                          flag_alloc_r;     // SR[F] allocated for write-back
  wire [DEST_EXTADR_WIDTH-1:0] flag_alloc_ext_m; // SR[F] allocation index
  reg  [DEST_EXTADR_WIDTH-1:0] flag_alloc_ext_r; // SR[F] allocation index
  // ---
  assign flag_alloc_w    = dcod_flag_we_i | flag_alloc_r;
  wire   keep_flag_alloc = dcod_flag_we_i | (flag_alloc_ext_r != wrbk_extadr_o);
  // ---
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i) begin
      flag_alloc_r <= 1'b0;
    end
    else begin
      if (flag_alloc_r)
        flag_alloc_r <= keep_flag_alloc;
      else if (padv_exec_i)
        flag_alloc_r <= dcod_flag_we_i;
    end
  end // at cpu-clock
  // ---
  assign flag_alloc_ext_m = dcod_flag_we_i ? dcod_extadr_r : flag_alloc_ext_r;
  // ---
  always @(posedge cpu_clk) begin
    if (padv_exec_i)
      flag_alloc_ext_r <= flag_alloc_ext_m;
  end // at cpu-clock

  // --- use / do  preticted or instant conditional branch (bc) ---
  wire fetch_op_bc = fetch_op_bf_i | fetch_op_bnf_i;
  reg  dcod_op_bc_r; // to WriteBack
  reg  dcod_op_bf_r; // to WriteBack
  reg  take_bc_r;    // to IFETCH
  // --- prediction related registers ---
  wire do_bc_predict_raw = bc_cnt_value_i[1];
  reg  predict_bc_taken_r;
  reg  predict_flag_value_r;
  reg  predict_flag_alloc_r;
  // --- wait completion writting to SR[F] ---
  wire keep_predict_flag_alloc = predict_flag_alloc_r & (jb_hazard_ext_p != wrbk_extadr_o);
  // --- compute raw hit/miss for prediction ---
  // --- they are used only inside J/B FSM ---
  wire predict_hit_raw  = (~predict_flag_alloc_r) &  (~(predict_flag_value_r ^ ctrl_flag_sr_i));
  wire predict_miss_raw = (~predict_flag_alloc_r) &    (predict_flag_value_r ^ ctrl_flag_sr_i);
  // --- complete prediction hit ---
  wire predict_hit = (bc_fsm_predict_catching_ds_state | bc_fsm_predict_waiting_flag_state) & predict_hit_raw;

  // Jump / Branch state machine
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i) begin
      bc_fsm_state_r       <= BC_FSM_CATCHING_BC; // flush pipe
      take_bc_r            <= 1'b0; // flush pipe
      dcod_op_bc_r         <= 1'b0; // flush pipe
      dcod_op_bf_r         <= 1'b0; // flush pipe
      predict_bc_taken_r   <= 1'b0; // flush pipe
      predict_flag_value_r <= 1'b0; // flush pipe
      predict_flag_alloc_r <= 1'b0; // flush pipe
    end
    else begin
      // synthesis parallel_case
      case (bc_fsm_state_r)
        // catching j/b on IFETCH output
        BC_FSM_CATCHING_BC: begin
          if (padv_dcod_i) begin
            if (fetch_op_bc) begin
              if (flag_alloc_w) begin
                bc_fsm_state_r        <= BC_FSM_PREDICT_CATCHING_DS;
                take_bc_r             <= do_bc_predict_raw;
                predict_bc_taken_r    <= do_bc_predict_raw;
                predict_flag_value_r  <= (fetch_op_bf_i  &   do_bc_predict_raw) | // PREDICTED FLAG
                                         (fetch_op_bnf_i & (~do_bc_predict_raw)); // PREDICTED FLAG
                predict_flag_alloc_r  <= keep_flag_alloc;
              end
              else begin
                bc_fsm_state_r <= BC_FSM_DO_INSTANT_BRANCH;
                take_bc_r      <= (fetch_op_bf_i  &   ctrl_flag_sr_i) |
                                  (fetch_op_bnf_i & (~ctrl_flag_sr_i));
              end
              dcod_op_bc_r <= 1'b1;
              dcod_op_bf_r <= fetch_op_bf_i;
            end
          end
        end

        // we can take branch without prediction
        BC_FSM_DO_INSTANT_BRANCH: begin
          bc_fsm_state_r <= BC_FSM_CATCHING_BC;
          take_bc_r      <= 1'b0;
          dcod_op_bc_r   <= 1'b0;
          dcod_op_bf_r   <= 1'b0;
        end

        // catching delay slot after branch conditional
        BC_FSM_PREDICT_CATCHING_DS: begin
          if (predict_hit_raw) begin
            bc_fsm_state_r <= BC_FSM_CATCHING_BC;
          end
          else if (padv_dcod_i) begin
            if (fetch_delay_slot_i)
              bc_fsm_state_r <= predict_miss_raw ? BC_FSM_PREDICT_MISS : BC_FSM_PREDICT_WAITING_FLAG;
          end
          predict_flag_alloc_r <= keep_predict_flag_alloc;
          take_bc_r            <= 1'b0;
          dcod_op_bc_r         <= 1'b0;
          dcod_op_bf_r         <= 1'b0;
         end
        // waiting flag computation
        BC_FSM_PREDICT_WAITING_FLAG: begin
          if (predict_hit_raw) begin
            bc_fsm_state_r <= BC_FSM_CATCHING_BC;
          end
          else if (predict_miss_raw) begin
            bc_fsm_state_r <= BC_FSM_PREDICT_MISS;
          end
          predict_flag_alloc_r <= keep_predict_flag_alloc;
        end
        // miss prediction (1-clock)
        BC_FSM_PREDICT_MISS: begin
          bc_fsm_state_r <= BC_FSM_CATCHING_BC;
        end

        // others
        default:;
      endcase
    end
  end // @cpu-clock


  // address extention for J/B processing
  always @(posedge cpu_clk) begin
    if (padv_dcod_i) begin
      if (jr_fsm_catching_jr & fetch_op_jr_i)
        jb_hazard_ext_p <= jr_dcd2fth_hazard_d1b1_raw ? dcod_extadr_r : jr_hazard_ext_raw;
      else if (bc_fsm_catching_bc & fetch_op_bc)
        jb_hazard_ext_p <= flag_alloc_ext_m;
    end
  end // at cpu clock
  // store target for l.jr/l.jalr
  always @(posedge cpu_clk) begin
    jr_target_p <=  jr_fsm_get_b1_state     ? dcod_rfb1_jr_i :
                   (jr_fsm_waiting_b1_state ? wrbk_result1_i   :
                                              jr_target_p);
  end // @cpu-clock


  // store target for miss prediction
  reg  [OPTION_OPERAND_WIDTH-1:0] predict_miss_target_r;
  // ---
  always @(posedge cpu_clk) begin
    if (padv_dcod_i) begin
      if (fetch_op_bc) begin
        predict_miss_target_r <= do_bc_predict_raw ? after_ds_target_i : fetch_to_imm_target_i;
      end
    end
  end // at clock


  // latch jump-to-immediate flag for 1-clock
  // to generate "do branch"
  reg                             dcod_op_jimm_r;
  reg  [OPTION_OPERAND_WIDTH-1:0] dcod_to_imm_target_r;
  // ---
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      dcod_op_jimm_r <= 1'b0;
    else if (padv_dcod_i)
      dcod_op_jimm_r <= fetch_op_jimm_i;
    else
      dcod_op_jimm_r <= 1'b0;
  end // at cpu clock
  // ---
  always @(posedge cpu_clk) begin
    if (padv_dcod_i)
      dcod_to_imm_target_r <= fetch_to_imm_target_i;
  end // at cpu clock


  // DECODE is "locked" flag.
  //  (1) We set the flag after delay slot has passed
  // into DECODE and till prediction resolving.
  //  (2) For l.jr/l.jalr we use another approach:
  // IFETCH just generates bubbles till rB1 hazard resolving.
  // ---
  reg  dcod_locked_r;
  // ---
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      dcod_locked_r <= 1'b0;
    else if (dcod_locked_r) begin
      if ((bc_fsm_predict_waiting_flag_state & predict_hit_raw) | // UNLOCK DECODE
          bc_fsm_predict_miss_state)                              // UNLOCK DECODE
        dcod_locked_r <= 1'b0;
    end
    else if (padv_dcod_i)
      dcod_locked_r <= fetch_delay_slot_i &                                     // LOCK DECODE
                       (bc_fsm_predict_catching_ds_state & (~predict_hit_raw)); // LOCK DECODE
  end // at clock
  // ---
  assign dcod_free_o = (~dcod_locked_r);



  // --- Feedback to IFETCH --- //


  // branch prediction missed
  assign predict_miss_o = bc_fsm_predict_miss_state;

  // "Do branch"
  assign do_branch_o = dcod_op_jimm_r        |    // do jump to immediate
                       take_bc_r             |    // do branch conditional
                       jr_fsm_doing_jr_state |    // do jump to register (B1)
                       bc_fsm_predict_miss_state; // do jump to mispredict target
  // branch target
  assign do_branch_target_o = bc_fsm_predict_miss_state ? predict_miss_target_r :  // branch target selection
                                   (jr_fsm_doing_jr_state ? jr_target_p :          // branch target selection
                                                            dcod_to_imm_target_r); // branch target selection

  // we execute l.jr/l.jalr after registering target only
  assign jr_gathering_target_o = (fetch_op_jb_i & (~bc_fsm_predict_miss_state)) | jr_gathering_target_p;



  // --- Feedforward to Write-Back --- //


  // JUMP/BRANCH attribute layout
  // --- data ---
  localparam  JB_ATTR_D_TARGET_LSB     = 0;
  localparam  JB_ATTR_D_TARGET_MSB     = OPTION_OPERAND_WIDTH     - 1;
  // --- control flags ---
  localparam  JB_ATTR_C_BF_POS         = JB_ATTR_D_TARGET_MSB     + 1; // conditional
  localparam  JB_ATTR_C_JUMP_POS       = JB_ATTR_C_BF_POS         + 1; // unconditional
  localparam  JB_ATTR_C_IBUS_ALIGN_POS = JB_ATTR_C_JUMP_POS       + 1;
  localparam  JB_ATTR_C_VALID_POS      = JB_ATTR_C_IBUS_ALIGN_POS + 1;
  // --- overall --
  localparam  JB_ATTR_MSB              = JB_ATTR_C_VALID_POS;
  localparam  JB_ATTR_WIDTH            = JB_ATTR_MSB + 1;

  // Write/Read to Jump/Branch attributes buffers
  // !!! each case is 1-clock length
  wire jb_attr_ocb_write = jr_fsm_doing_jr_state | dcod_op_jimm_r | dcod_op_bc_r;
  wire jb_attr_ocb_read  = padv_wrbk_i & ocbo[OCBTC_JUMP_OR_BRANCH_POS];

  // --- JB-ATTR-OCB output / input ---
  wire [JB_ATTR_MSB:0] jb_attr_ocbo;
  wire [JB_ATTR_MSB:0] jb_attr_ocbi;
  // ---
  assign jb_attr_ocbi =
    {
      // --- control flags ---
      1'b1, // JB ATTR-C VALID
      (jr_fsm_doing_jr_state & (|jr_target_p[1:0])), // JB ATTR-C IBUS ALIGN
      (jr_fsm_doing_jr_state | dcod_op_jimm_r), // JB ATTR-C JUMP (uncoditional)
      dcod_op_bf_r, // JB ATTR-C BRANCH BY FLAG (conditional)
      // --- data ---
      (jr_fsm_doing_jr_state ? jr_target_p : dcod_to_imm_target_r) // JB ATTR-D TARGET
    };

  // --- JB-ATTR-OCB instance ---
  mor1kx_ff_oreg_buff_marocchino
  #(
    .NUM_TAPS         (JB_ATTR_OCB_NUM_TAPS), // JB-ATTR-OCB: extention bits "0" is reserved as "not used"
    .DATA_WIDTH       (JB_ATTR_WIDTH), // JB-ATTR-OCB
    .FULL_FLAG        ("NONE"), // JB-ATTR-OCB
    .EMPTY_FLAG       ("NONE") // JB-ATTR-OCB
  )
  u_jb_attr_ocb
  (
    // clocks, resets
    .cpu_clk          (cpu_clk), // JB-ATTR-OCB
    // resets
    .ini_rst          (pipeline_flush_i), // JB-ATTR-OCB
    .ext_rst          (1'b0), // JB-ATTR-OCB
    // RW-controls
    .write_i          (jb_attr_ocb_write), // JB-ATTR-OCB
    .read_i           (jb_attr_ocb_read), // JB-ATTR-OCB
    // data input
    .data_i           (jb_attr_ocbi), // JB-ATTR-OCB
    // "OCB is empty" flag
    .empty_o          (), // JB-ATTR-OCB
    // "OCB is full" flag
    .full_o           (), // JB-ATTR-OCB
    // output register
    .data_o           (jb_attr_ocbo) // JB-ATTR-OCB
  );

  // --- JB-ATTR-OCB valid unpack ---
  assign exec_jb_attr_valid = jb_attr_ocbo[JB_ATTR_C_VALID_POS];



  //----------------------------------------//
  // Saturation counter as branch predictor //
  //----------------------------------------//
  //  (a) We update counter only after completion
  //      all previous updates of SR[F]
  //  (b) They are 1-clock length to prevent multiple
  //      updates of counter

  // --- pending values for update saturation counters and branch history ---
  reg                    [1:0] bc_cnt_value_up_p;
  reg                    [1:0] bc_cnt_value_dn_p;
  reg  [(GSHARE_BITS_NUM-1):0] bc_cnt_radr_p;
  // --- pre-computed up and down next values of saturation counter ---
  wire [1:0] bc_cnt_value_up = (bc_cnt_value_i == 2'b11) ? bc_cnt_value_i : (bc_cnt_value_i + 1'b1);
  wire [1:0] bc_cnt_value_dn = (bc_cnt_value_i == 2'b00) ? bc_cnt_value_i : (bc_cnt_value_i - 1'b1);
  // --- data for update saturation counters and branch history ---
  always @(posedge cpu_clk) begin
    if (padv_dcod_i & (fetch_op_bf_i | fetch_op_bnf_i)) begin // PENDING FOR SATURATION COUNTERS
      bc_cnt_value_up_p <= bc_cnt_value_up; // PENDING FOR SATURATION COUNTERS
      bc_cnt_value_dn_p <= bc_cnt_value_dn; // PENDING FOR SATURATION COUNTERS
      bc_cnt_radr_p     <= bc_cnt_radr_i;   // PENDING FOR SATURATION COUNTERS
    end
  end

  // --- write to saturation counters and branch history (1-clock) ---
  //     !!! use-bc-instant-p couldn't be overlapped by predict
  //     !!! resolving events (from prev. l.bf/l.bnf) because
  //     !!! DECODE is locked till prediction resolving
  always @(posedge cpu_clk) begin
    if (cpu_rst)
      bc_cnt_we_o <= 1'b0;
    else if (bc_fsm_do_instant_branch_state | predict_hit | bc_fsm_predict_miss_state)
      bc_cnt_we_o <= 1'b1;
    else
      bc_cnt_we_o <= 1'b0;
  end // at clock
  // --- saturation counter update address ---
  always @(posedge cpu_clk) begin
    if (bc_fsm_do_instant_branch_state | predict_hit | bc_fsm_predict_miss_state)
      bc_cnt_wadr_o <= bc_cnt_radr_p;
  end // at clock
  // --- data for saturation counters and branch history ---
  always @(posedge cpu_clk) begin
    if (bc_fsm_do_instant_branch_state) begin
      bc_hist_taken_o <= take_bc_r;
      bc_cnt_wdat_o   <= take_bc_r ? bc_cnt_value_up_p : bc_cnt_value_dn_p;
    end
    else if (predict_hit) begin
      bc_hist_taken_o <= predict_bc_taken_r;
      bc_cnt_wdat_o   <= predict_bc_taken_r ? bc_cnt_value_up_p : bc_cnt_value_dn_p;
    end
    else if (bc_fsm_predict_miss_state) begin
      bc_hist_taken_o <= (~predict_bc_taken_r);
      bc_cnt_wdat_o   <= (~predict_bc_taken_r) ? bc_cnt_value_up_p : bc_cnt_value_dn_p;
    end
  end // at clock



  //--------------------//
  // Write Back latches //
  //--------------------//

  // Write-Back JUMP or BRANCH attributes
  //  # flags (all 1-clock length)
  always @(posedge cpu_clk) begin
    if (padv_wrbk_i) begin
      wrbk_jump_or_branch_o <= ocbo[OCBTC_JUMP_OR_BRANCH_POS];
      wrbk_jump_o           <= jb_attr_ocbo[JB_ATTR_C_JUMP_POS];
      wrbk_op_bf_o          <= jb_attr_ocbo[JB_ATTR_C_BF_POS];
    end
    else begin
      wrbk_jump_or_branch_o <= 1'b0;
      wrbk_jump_o           <= 1'b0;
      wrbk_op_bf_o          <= 1'b0;
    end
  end // @clock
  //  # target
  always @(posedge cpu_clk) begin
    if (padv_wrbk_i)
      wrbk_jb_target_o <= jb_attr_ocbo[JB_ATTR_D_TARGET_MSB:JB_ATTR_D_TARGET_LSB];
  end // @clock



  //   Flag to enabel/disable exterlal interrupts processing
  // depending on the fact is instructions restartable or not
  assign exec_interrupts_en_o     = ocbo[OCBTA_INTERRUPTS_EN_POS];

  // pre-Write-Back l.rfe
  assign exec_op_rfe_o            = ocbo[OCBTA_OP_RFE_POS];
  // IFETCH/DECODE an exception
  assign exec_an_except_fd_o      = ocbo[OCBTA_AN_EXCEPT_FD_POS];
  // IFETCH exceptions
  assign exec_except_ibus_err_o   = ocbo[5];
  assign exec_except_ipagefault_o = ocbo[4];
  assign exec_except_itlb_miss_o  = ocbo[3];
  assign exec_except_ibus_align_o = jb_attr_ocbo[JB_ATTR_C_IBUS_ALIGN_POS];
  // DECODE exceptions
  assign exec_except_illegal_o    = ocbo[2];
  assign exec_except_syscall_o    = ocbo[1];
  assign exec_except_trap_o       = ocbo[0];

  // PC at EXECUTE (moslty for debugging)
  wire [OPTION_OPERAND_WIDTH-1:0] pc_exec = ocbo[OCBTA_PC_MSB:OCBTA_PC_LSB];

  // instuction requests write-back
  wire exec_rfd1_we = ocbo[OCBTA_RFD1_WRBK_POS];
  wire exec_rfd2_we = ocbo[OCBTA_RFD2_WRBK_POS];

  // destiny addresses
  wire [OPTION_RF_ADDR_WIDTH-1:0] exec_rfd1_adr = ocbo[OCBTA_RFD1_ADR_MSB:OCBTA_RFD1_ADR_LSB];
  wire [OPTION_RF_ADDR_WIDTH-1:0] exec_rfd2_adr = ocbo[OCBTA_RFD2_ADR_MSB:OCBTA_RFD2_ADR_LSB];


  // 1-hot Write-Back-controls for RF
  //  if A(B)'s address is odd than A2(B2)=A(B)+1 is even and vise verse
  //  1-clock Write-Back-pulses
  always @(posedge cpu_clk) begin
    if (padv_wrbk_i) begin
      wrbk_rfd1_we1h_o <= {{(NUM_GPRS-1){1'b0}},exec_rfd1_we} << exec_rfd1_adr;
      wrbk_rfd1_we_o   <= exec_rfd1_we;
      wrbk_rfd2_we1h_o <= {{(NUM_GPRS-1){1'b0}},exec_rfd2_we} << exec_rfd2_adr;
      wrbk_rfd2_we_o   <= exec_rfd2_we;
    end
    else begin
      wrbk_rfd1_we1h_o <= {NUM_GPRS{1'b0}};
      wrbk_rfd1_we_o   <= 1'b0;
      wrbk_rfd2_we1h_o <= {NUM_GPRS{1'b0}};
      wrbk_rfd2_we_o   <= 1'b0;
    end
  end // @clock
  // latch write-back addresses without reset
  always @(posedge cpu_clk) begin
    if (padv_wrbk_i) begin
      wrbk_rfd1_adr_o <= exec_rfd1_adr;
      wrbk_rfd2_adr_o <= exec_rfd2_adr;
    end
  end // @clock



  // Write-Back delay slot
  always @(posedge cpu_clk) begin
    if (padv_wrbk_i)
      wrbk_delay_slot_o <= ocbo[OCBTA_DELAY_SLOT_POS];
    else
      wrbk_delay_slot_o <= 1'b0;
  end // @clock


  // extention bits: valid for 1-clock
  // to reolve hazards in rezervation stations
  always @(posedge cpu_clk) begin
    if (padv_wrbk_i)
      wrbk_extadr_o <= exec_extadr;
    else
      wrbk_extadr_o <= {DEST_EXTADR_WIDTH{1'b0}};
  end // @clock


  // PC
  always @(posedge cpu_clk) begin
    if (padv_wrbk_i) begin
      pc_wrbk_o      <= pc_exec;
      pc_nxt_wrbk_o  <= pc_exec + 3'd4;
      pc_nxt2_wrbk_o <= pc_exec + 4'd8;
    end
  end // @clock

endmodule // mor1kx_oman_marocchino
