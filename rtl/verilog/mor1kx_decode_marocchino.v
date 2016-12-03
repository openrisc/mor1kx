////////////////////////////////////////////////////////////////////////
//                                                                    //
//  mor1kx_decode_marocchino                                          //
//                                                                    //
//  Description: mor1kx decode unit for MAROCCHINO pipeline           //
//               Derived from mor1kx_decode and                       //
//                            mor1kx_decode_execute_cappuccino        //
//  Outputs:                                                          //
//   - ALU operation                                                  //
//   - indication of other type of op - LSU/SPR                       //
//   - immediates                                                     //
//   - register file addresses                                        //
//   - exception decodes:  illegal, system call                       //
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

module mor1kx_decode_marocchino
#(
  parameter OPTION_OPERAND_WIDTH = 32,
  parameter OPTION_RESET_PC      = {{(OPTION_OPERAND_WIDTH-13){1'b0}},
                                    `OR1K_RESET_VECTOR,8'd0},
  parameter OPTION_RF_ADDR_WIDTH =  5,

  parameter FEATURE_PSYNC        = "NONE",
  parameter FEATURE_CSYNC        = "NONE"
)
(
  // INSN
  input          [`OR1K_INSN_WIDTH-1:0] dcod_insn_i,

  // Data dependancy detection
  output                                dcod_op_jr_o,
  input                                 exe2dec_hazard_d1b1_i,

  // PC
  input      [OPTION_OPERAND_WIDTH-1:0] pc_decode_i,
  // IMM
  output     [OPTION_OPERAND_WIDTH-1:0] dcod_immediate_o,
  output                                dcod_immediate_sel_o,

  // various instruction attributes
  output reg                            dcod_rfa1_req_o, // instruction requires operand A
  output reg                            dcod_rfb1_req_o, // instruction requires operand B
  output reg                            dcod_rfd1_wb_o,   // instruction performes WB
  output     [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfd1_adr_o, // address of WB
  output                                dcod_flag_wb_o,   // instruction writes comparison flag
  output                                dcod_carry_wb_o,  // instruction writes carry flag
  output                                dcod_flag_req_o,  // instruction requires comparison flag
  output                                dcod_carry_req_o, // instruction requires carry flag
  // for FPU64
  output reg                            dcod_rfa2_req_o, // instruction requires operand A2
  output reg                            dcod_rfb2_req_o, // instruction requires operand B2

  // flag & branches
  output                                dcod_jump_or_branch_o, // detect jump/branch to indicate "delay slot" for next fetched instruction
  // Forwarding comparision flag
  input                                 exec_op_1clk_cmp_i, // integer or fp32
  input                                 exec_flag_set_i,    // integer or fp32 comparison result
  input                                 ctrl_flag_i,
  // Do jump/branch and jump/branch target for FETCH
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_rfb1_i,
  output                                dcod_do_branch_o,
  output     [OPTION_OPERAND_WIDTH-1:0] dcod_do_branch_target_o,

  // Signals to stall FETCH if we are waiting flag
  //  # flag is going to be written by multi-cycle instruction
  //  # like 64-bit FPU comparison or l.swa
  output                                dcod_flag_wb_mcycle_o,
  //  # conditional branch: l.bf or l.bnf
  output                                dcod_op_brcond_o,

  // LSU related
  output          [`OR1K_IMM_WIDTH-1:0] dcod_imm16_o,
  output                                dcod_op_lsu_load_o,
  output                                dcod_op_lsu_store_o,
  output                                dcod_op_lsu_atomic_o,
  output reg                      [1:0] dcod_lsu_length_o,
  output                                dcod_lsu_zext_o,
  output                                dcod_op_msync_o,

  // Instruction which passes EXECUTION through
  output reg                            dcod_op_pass_exec_o,

  // 1-clock instruction
  output reg                            dcod_op_1clk_o,
  // ALU related opc
  output      [`OR1K_ALU_OPC_WIDTH-1:0] dcod_opc_alu_secondary_o,
  // Adder related
  output                                dcod_op_add_o,
  output                                dcod_adder_do_sub_o,
  output                                dcod_adder_do_carry_o,
  // Various 1-clock related
  output                                dcod_op_shift_o,
  output                                dcod_op_ffl1_o,
  output                                dcod_op_movhi_o,
  output                                dcod_op_cmov_o,
  // Logic
  output      [`OR1K_ALU_OPC_WIDTH-1:0] dcod_opc_logic_o,
  // Jump & Link
  output                                dcod_op_jal_o,
  output     [OPTION_OPERAND_WIDTH-1:0] dcod_jal_result_o,
  // Set flag related
  output                                dcod_op_setflag_o,
  output                                dcod_op_fp32_cmp_o,
  output                          [2:0] dcod_opc_fp32_cmp_o,

  // Multiplier related
  output                                dcod_op_mul_o,

  // Divider related
  output                                dcod_op_div_o, // (not latched, to OMAN)
  output                                dcod_op_div_signed_o,
  output                                dcod_op_div_unsigned_o,

  // FPU3264 arithmetic part
  output                                dcod_op_fpxx_arith_o, // to OMAN and FPU3264_ARITH
  output                                dcod_op_fp64_arith_o, // to FPU3264_ARITH
  output                                dcod_op_fpxx_add_o, // to FPU3264_ARITH
  output                                dcod_op_fpxx_sub_o, // to FPU3264_ARITH
  output                                dcod_op_fpxx_mul_o, // to FPU3264_ARITH
  output                                dcod_op_fpxx_div_o, // to FPU3264_ARITH
  output                                dcod_op_fpxx_i2f_o, // to FPU3264_ARITH
  output                                dcod_op_fpxx_f2i_o, // to FPU3264_ARITH

  // FPU-64 comparison part
  output                                dcod_op_fp64_cmp_o,
  output                          [2:0] dcod_opc_fp64_cmp_o,

  // MTSPR / MFSPR
  output                                dcod_op_mfspr_o,
  output                                dcod_op_mtspr_o,

  // Exceptions detected on decode stage flags
  //  ## enable l.trap exception
  input                                 du_trap_enable_i,
  //  ## outcome exception flags
  output                                fetch_except_ibus_align_o,
  output reg                            dcod_except_illegal_o,
  output                                dcod_except_syscall_o,
  output                                dcod_except_trap_o,

  // RFE
  output                                dcod_op_rfe_o
);

  wire [OPTION_OPERAND_WIDTH-1:0] imm_sext;
  wire                            imm_sext_sel;
  wire [OPTION_OPERAND_WIDTH-1:0] imm_zext;
  wire                            imm_zext_sel;
  wire [OPTION_OPERAND_WIDTH-1:0] imm_high;
  wire                            imm_high_sel;

  // Insn opcode
  wire [`OR1K_OPCODE_WIDTH-1:0]  opc_insn = dcod_insn_i[`OR1K_OPCODE_SELECT];
  wire [`OR1K_ALU_OPC_WIDTH-1:0] opc_alu  = dcod_insn_i[`OR1K_ALU_OPC_SELECT];

  wire dcod_op_alu = (opc_insn == `OR1K_OPCODE_ALU);


  // load opcodes are 6'b10_0000 to 6'b10_0110, 0 to 6, so check for 7 and up
  assign dcod_op_lsu_load_o = (opc_insn == `OR1K_OPCODE_LWA) |
                              ((opc_insn == `OR1K_OPCODE_LD) & (OPTION_OPERAND_WIDTH == 64)) |
                              ((opc_insn >= `OR1K_OPCODE_LWZ) & (opc_insn <= `OR1K_OPCODE_LHS));

  // Detect when instruction is store
  assign dcod_op_lsu_store_o = (opc_insn == `OR1K_OPCODE_SW) | (opc_insn == `OR1K_OPCODE_SB)  |
                               (opc_insn == `OR1K_OPCODE_SH) | (opc_insn == `OR1K_OPCODE_SWA) |
                               ((opc_insn == `OR1K_OPCODE_SD) & (OPTION_OPERAND_WIDTH == 64));

  assign dcod_op_lsu_atomic_o = (opc_insn == `OR1K_OPCODE_LWA) | (opc_insn == `OR1K_OPCODE_SWA);


  // Decode length of load/store operation
  always @(opc_insn)
    // synthesis parallel_case full_case
    case (opc_insn)
      // byte
      `OR1K_OPCODE_SB,
      `OR1K_OPCODE_LBZ,
      `OR1K_OPCODE_LBS: dcod_lsu_length_o = 2'b00;
      // half word
      `OR1K_OPCODE_SH,
      `OR1K_OPCODE_LHZ,
      `OR1K_OPCODE_LHS: dcod_lsu_length_o = 2'b01;
      // word
      `OR1K_OPCODE_SW,
      `OR1K_OPCODE_SWA,
      `OR1K_OPCODE_LWZ,
      `OR1K_OPCODE_LWS,
      `OR1K_OPCODE_LWA: dcod_lsu_length_o = 2'b10;
      // default
      default:          dcod_lsu_length_o = 2'b10;
  endcase

  assign dcod_lsu_zext_o = opc_insn[0];

  assign dcod_op_msync_o = (opc_insn == `OR1K_OPCODE_SYSTRAPSYNC) &
                           (dcod_insn_i[`OR1K_SYSTRAPSYNC_OPC_SELECT] ==
                            `OR1K_SYSTRAPSYNC_OPC_MSYNC);

  assign dcod_op_mtspr_o = (opc_insn == `OR1K_OPCODE_MTSPR);
  assign dcod_op_mfspr_o  = (opc_insn == `OR1K_OPCODE_MFSPR);

  // Detect when setflag instruction
  assign dcod_op_setflag_o = (opc_insn == `OR1K_OPCODE_SF) |
                             (opc_insn == `OR1K_OPCODE_SFIMM);


  // --- adder ---
  assign dcod_op_add_o = (dcod_op_alu &
                          ((opc_alu == `OR1K_ALU_OPC_ADDC) |
                          (opc_alu == `OR1K_ALU_OPC_ADD) |
                          (opc_alu == `OR1K_ALU_OPC_SUB))) |
                         (opc_insn == `OR1K_OPCODE_ADDIC) |
                         (opc_insn == `OR1K_OPCODE_ADDI);
  // Adder control logic
  // Subtract when comparing to check if equal
  assign dcod_adder_do_sub_o = (dcod_op_alu & (opc_alu == `OR1K_ALU_OPC_SUB)) |
                               dcod_op_setflag_o;
  // Generate carry-in select
  assign dcod_adder_do_carry_o = (dcod_op_alu & (opc_alu == `OR1K_ALU_OPC_ADDC)) |
                                 (opc_insn == `OR1K_OPCODE_ADDIC);


  // --- multiplier ---
  wire dcod_op_mul_signed = (dcod_op_alu & (opc_alu == `OR1K_ALU_OPC_MUL)) |
                            (opc_insn == `OR1K_OPCODE_MULI);

  wire dcod_op_mul_unsigned = dcod_op_alu & (opc_alu == `OR1K_ALU_OPC_MULU);

  assign dcod_op_mul_o = dcod_op_mul_signed | dcod_op_mul_unsigned;


  // --- divider ---
  assign dcod_op_div_signed_o = dcod_op_alu & (opc_alu == `OR1K_ALU_OPC_DIV);

  assign dcod_op_div_unsigned_o = dcod_op_alu & (opc_alu == `OR1K_ALU_OPC_DIVU);

  assign dcod_op_div_o = dcod_op_div_signed_o | dcod_op_div_unsigned_o;


  // --- shifter / ffl1 / movhi / cmov ---
  assign dcod_op_shift_o = (dcod_op_alu & (opc_alu  == `OR1K_ALU_OPC_SHRT)) |
                           (opc_insn == `OR1K_OPCODE_SHRTI);

  assign dcod_op_ffl1_o  = dcod_op_alu & (opc_alu  == `OR1K_ALU_OPC_FFL1);

  assign dcod_op_movhi_o = (opc_insn == `OR1K_OPCODE_MOVHI);

  assign dcod_op_cmov_o  = (dcod_op_alu & (opc_alu == `OR1K_ALU_OPC_CMOV));


  // --- logic ---
  assign dcod_opc_logic_o =
    (((opc_insn == `OR1K_OPCODE_ALU) & (opc_alu == `OR1K_ALU_OPC_OR )) | (opc_insn == `OR1K_OPCODE_ORI )) ? `OR1K_ALU_OPC_OR  :
    (((opc_insn == `OR1K_OPCODE_ALU) & (opc_alu == `OR1K_ALU_OPC_XOR)) | (opc_insn == `OR1K_OPCODE_XORI)) ? `OR1K_ALU_OPC_XOR :
    (((opc_insn == `OR1K_OPCODE_ALU) & (opc_alu == `OR1K_ALU_OPC_AND)) | (opc_insn == `OR1K_OPCODE_ANDI)) ? `OR1K_ALU_OPC_AND :
                                                                                                   {`OR1K_ALU_OPC_WIDTH{1'b0}};


  // --- FPU-32 comparison part ---
  //  # for further legality detection
  wire op_fp32_cmp_l = (~dcod_insn_i[`OR1K_FPUOP_DOUBLE_BIT]) & dcod_insn_i[3] &
                       (~(|dcod_insn_i[10:8])) & // all reserved bits are zeros
                       (dcod_insn_i[2:0] < 3'd6);
  //  # directly for FPU32 execution unit
  assign dcod_op_fp32_cmp_o = op_fp32_cmp_l & (opc_insn == `OR1K_OPCODE_FPU);
  // fpu comparison opc:
  // ===================
  // 000 = EQ
  // 001 = NE
  // 010 = GT
  // 011 = GE
  // 100 = LT
  // 101 = LE
  assign dcod_opc_fp32_cmp_o = dcod_insn_i[2:0];


  // --- FPU3264 arithmetic part ---
  //  # tmp skeleton
  wire op_fpxx_arith_t = (~dcod_insn_i[3]) &        // arithmetic operation
                         (~(|dcod_insn_i[10:8]));   // all reserved bits are zeros
  //  # for further legality detection
  wire op_fpxx_arith_l = op_fpxx_arith_t & (dcod_insn_i[2:0] < 3'd6);
  //  # a legal FPU
  assign dcod_op_fpxx_arith_o = op_fpxx_arith_l & (opc_insn == `OR1K_OPCODE_FPU);
  //  # directly for FPU3264 execution unit
  assign dcod_op_fp64_arith_o = dcod_insn_i[`OR1K_FPUOP_DOUBLE_BIT];
  // fpu arithmetic opc:
  // ===================
  // 000 = add
  // 001 = substract
  // 010 = multiply
  // 011 = divide
  // 100 = i2f
  // 101 = f2i
  assign dcod_op_fpxx_add_o = op_fpxx_arith_t & (dcod_insn_i[2:0] == 3'd0) & (opc_insn == `OR1K_OPCODE_FPU);
  assign dcod_op_fpxx_sub_o = op_fpxx_arith_t & (dcod_insn_i[2:0] == 3'd1) & (opc_insn == `OR1K_OPCODE_FPU);
  assign dcod_op_fpxx_mul_o = op_fpxx_arith_t & (dcod_insn_i[2:0] == 3'd2) & (opc_insn == `OR1K_OPCODE_FPU);
  assign dcod_op_fpxx_div_o = op_fpxx_arith_t & (dcod_insn_i[2:0] == 3'd3) & (opc_insn == `OR1K_OPCODE_FPU);
  assign dcod_op_fpxx_i2f_o = op_fpxx_arith_t & (dcod_insn_i[2:0] == 3'd4) & (opc_insn == `OR1K_OPCODE_FPU);
  assign dcod_op_fpxx_f2i_o = op_fpxx_arith_t & (dcod_insn_i[2:0] == 3'd5) & (opc_insn == `OR1K_OPCODE_FPU);


  // --- FPU-64 comparison part ---
  //  # for further legality detection
  wire op_fp64_cmp_l = dcod_insn_i[`OR1K_FPUOP_DOUBLE_BIT] & dcod_insn_i[3] &
                       (~(|dcod_insn_i[10:8])) & // all reserved bits are zeros
                       (dcod_insn_i[2:0] < 3'd6);
  //  # directly for FPU32 execution unit
  assign dcod_op_fp64_cmp_o = op_fp64_cmp_l & (opc_insn == `OR1K_OPCODE_FPU);
  // fpu comparison opc:
  // ===================
  // 000 = EQ
  // 001 = NE
  // 010 = GT
  // 011 = GE
  // 100 = LT
  // 101 = LE
  assign dcod_opc_fp64_cmp_o = dcod_insn_i[2:0];


  // Immediate in l.mtspr is broken up, reassemble
  assign dcod_imm16_o = (dcod_op_mtspr_o | dcod_op_lsu_store_o) ?
                        {dcod_insn_i[25:21],dcod_insn_i[10:0]} :
                        dcod_insn_i[`OR1K_IMM_SELECT];

  //   Instructions with sign-extended immediate
  // excluding load/store, because LSU performs this extention by itself.
  assign imm_sext     = {{16{dcod_imm16_o[15]}}, dcod_imm16_o};
  assign imm_sext_sel = (opc_insn == `OR1K_OPCODE_ADDI)  |
                        (opc_insn == `OR1K_OPCODE_ADDIC) |
                        (opc_insn == `OR1K_OPCODE_XORI)  |
                        (opc_insn == `OR1K_OPCODE_MULI)  |
                        (opc_insn == `OR1K_OPCODE_SFIMM);

  //   Instructions with zero-extended immediate
  // excluding MT(F)SPR, because CTRL performs this extention by itself.
  assign imm_zext     = {16'd0, dcod_imm16_o};
  assign imm_zext_sel = (opc_insn == `OR1K_OPCODE_ORI)  |
                        (opc_insn == `OR1K_OPCODE_ANDI) |
                        (opc_insn == `OR1K_OPCODE_SHRTI);

  // l.movhi
  assign imm_high     = {dcod_insn_i[`OR1K_IMM_SELECT], 16'd0};
  assign imm_high_sel = dcod_op_movhi_o;

  // Use immediate flag and sign/zero extended Imm16
  assign dcod_immediate_o     = imm_sext_sel ? imm_sext :
                                imm_zext_sel ? imm_zext :
                                               imm_high;
  assign dcod_immediate_sel_o = imm_sext_sel | imm_zext_sel | imm_high_sel;


  // ALU related secondary opcode
  assign dcod_opc_alu_secondary_o = dcod_op_setflag_o ?
                                      dcod_insn_i[`OR1K_COMP_OPC_SELECT]:
                                      {1'b0,dcod_insn_i[`OR1K_ALU_OPC_SECONDARY_SELECT]};


  // Exceptions and l.rfe
  assign dcod_op_rfe_o = (opc_insn == `OR1K_OPCODE_RFE);

  assign dcod_except_syscall_o = (opc_insn == `OR1K_OPCODE_SYSTRAPSYNC) &
                                 (dcod_insn_i[`OR1K_SYSTRAPSYNC_OPC_SELECT] ==
                                  `OR1K_SYSTRAPSYNC_OPC_SYSCALL);

  assign dcod_except_trap_o = (opc_insn == `OR1K_OPCODE_SYSTRAPSYNC) &
                              (dcod_insn_i[`OR1K_SYSTRAPSYNC_OPC_SELECT] ==
                               `OR1K_SYSTRAPSYNC_OPC_TRAP) &
                              du_trap_enable_i;


  // Illegal instruction decode
  // Instruction executed during 1 clock
  // Instruction which passes EXECUTION through
  always @* begin
    // synthesis parallel_case full_case
    case (opc_insn)
      `OR1K_OPCODE_J,     // pc <- pc + exts(Imm26 << 2)
      `OR1K_OPCODE_JR,    // pc <- rB
      `OR1K_OPCODE_JAL,   // pc <- pc + exts(Imm26 << 2)
      `OR1K_OPCODE_JALR,  // pc <- rB
      `OR1K_OPCODE_BNF,   // pc <- pc + exts(Imm26 << 2) if ~flag
      `OR1K_OPCODE_BF:    // pc <- pc + exts(Imm26 << 2) if flag
        begin
          dcod_except_illegal_o = 1'b0;
          dcod_op_1clk_o        = dcod_op_jal_o; // save GPR[9] by l.jal/l.jalr
          dcod_op_pass_exec_o   = ~dcod_op_jal_o;
          dcod_rfa1_req_o       = 1'b0;
          dcod_rfb1_req_o       = dcod_op_jr_o;  // l.jr/l.jalr
          dcod_rfd1_wb_o        = dcod_op_jal_o; // save GPR[9] by l.jal/l.jalr
          // for FPU64
          dcod_rfa2_req_o       = 1'b0;
          dcod_rfb2_req_o       = 1'b0;
        end

      `OR1K_OPCODE_MOVHI, // rD <- {Imm16,16'd0}
      `OR1K_OPCODE_RFE,
      `OR1K_OPCODE_NOP:
        begin
          dcod_except_illegal_o = 1'b0;
          dcod_op_1clk_o        = dcod_op_movhi_o;
          dcod_op_pass_exec_o   = ~dcod_op_movhi_o;
          dcod_rfa1_req_o       = 1'b0;
          dcod_rfb1_req_o       = 1'b0;
          dcod_rfd1_wb_o        = dcod_op_movhi_o;
          // for FPU64
          dcod_rfa2_req_o       = 1'b0;
          dcod_rfb2_req_o       = 1'b0;
        end

      `OR1K_OPCODE_ADDI,  // rD <- rA + exts(Imm16)
      `OR1K_OPCODE_ADDIC, // rD <- rA + exts(Imm16) + carry
      `OR1K_OPCODE_ANDI,  // rD <- rA & extz(Imm16)
      `OR1K_OPCODE_ORI,   // rD <- rA | extz(Imm16)
      `OR1K_OPCODE_XORI,  // rD <- rA ^ exts(Imm16)
      `OR1K_OPCODE_MULI,  // rD <- rA * exts(Imm16)
      `OR1K_OPCODE_SF,    // SR[F] <- rA cmp rB
      `OR1K_OPCODE_SFIMM: // SR[F] <- rA cmp exts(Imm16)
        begin
          dcod_except_illegal_o = 1'b0;
          dcod_op_1clk_o        = (opc_insn != `OR1K_OPCODE_MULI);
          dcod_op_pass_exec_o   = 1'b0;
          dcod_rfa1_req_o       = 1'b1;
          dcod_rfb1_req_o       = (opc_insn == `OR1K_OPCODE_SF);
          dcod_rfd1_wb_o        = (opc_insn != `OR1K_OPCODE_SF) & (opc_insn != `OR1K_OPCODE_SFIMM);
          // for FPU64
          dcod_rfa2_req_o       = 1'b0;
          dcod_rfb2_req_o       = 1'b0;
        end

      `OR1K_OPCODE_MFSPR, // rD <- SPR(rA | extz(Imm16))
      `OR1K_OPCODE_LWZ,   // rD <- MEM(rA + exts(Imm16))
      `OR1K_OPCODE_LWS,   // rD <- MEM(rA + exts(Imm16))
      `OR1K_OPCODE_LBZ,   // rD <- MEM(rA + exts(Imm16))
      `OR1K_OPCODE_LBS,   // rD <- MEM(rA + exts(Imm16))
      `OR1K_OPCODE_LHZ,   // rD <- MEM(rA + exts(Imm16))
      `OR1K_OPCODE_LHS,   // rD <- MEM(rA + exts(Imm16))
      `OR1K_OPCODE_LWA:   // rD <- MEM(rA + exts(Imm16))
        begin
          dcod_except_illegal_o = 1'b0;
          dcod_op_1clk_o        = 1'b0;
          dcod_op_pass_exec_o   = 1'b0;
          dcod_rfa1_req_o       = 1'b1;
          dcod_rfb1_req_o       = 1'b0;
          dcod_rfd1_wb_o        = 1'b1;
          // for FPU64
          dcod_rfa2_req_o       = 1'b0;
          dcod_rfb2_req_o       = 1'b0;
        end

      `OR1K_OPCODE_LD:  // rD <- MEM(rA + exts(Imm16))
         begin
          dcod_except_illegal_o = (OPTION_OPERAND_WIDTH != 64);
          dcod_op_1clk_o        = 1'b0;
          dcod_op_pass_exec_o   = 1'b0;
          dcod_rfa1_req_o       = (OPTION_OPERAND_WIDTH == 64);
          dcod_rfb1_req_o       = 1'b0;
          dcod_rfd1_wb_o        = (OPTION_OPERAND_WIDTH == 64);
          // for FPU64
          dcod_rfa2_req_o       = 1'b0;
          dcod_rfb2_req_o       = 1'b0;
         end

      `OR1K_OPCODE_MTSPR, // rB -> SPR(rA | extz(Imm16))
      `OR1K_OPCODE_SW,    // rB -> MEM(rA + exts(Imm16))
      `OR1K_OPCODE_SB,    // rB -> MEM(rA + exts(Imm16))
      `OR1K_OPCODE_SH,    // rB -> MEM(rA + exts(Imm16))
      `OR1K_OPCODE_SWA:   // rB -> MEM(rA + exts(Imm16))
        begin
          dcod_except_illegal_o = 1'b0;
          dcod_op_1clk_o        = 1'b0;
          dcod_op_pass_exec_o   = 1'b0;
          dcod_rfa1_req_o       = 1'b1;
          dcod_rfb1_req_o       = 1'b1;
          dcod_rfd1_wb_o        = 1'b0;
          // for FPU64
          dcod_rfa2_req_o       = 1'b0;
          dcod_rfb2_req_o       = 1'b0;
        end

      `OR1K_OPCODE_SD:  // rB -> MEM(rA + exts(Imm16))
        begin
          dcod_except_illegal_o = (OPTION_OPERAND_WIDTH != 64);
          dcod_op_1clk_o        = 1'b0;
          dcod_op_pass_exec_o   = 1'b0;
          dcod_rfa1_req_o       = (OPTION_OPERAND_WIDTH == 64);
          dcod_rfb1_req_o       = (OPTION_OPERAND_WIDTH == 64);
          dcod_rfd1_wb_o        = 1'b0;
          // for FPU64
          dcod_rfa2_req_o       = 1'b0;
          dcod_rfb2_req_o       = 1'b0;
        end

      `OR1K_OPCODE_FPU:
        begin
          dcod_except_illegal_o = ~(op_fpxx_arith_l | op_fp32_cmp_l | op_fp64_cmp_l);
          dcod_op_pass_exec_o   = 1'b0;
          if (op_fpxx_arith_l) begin
            dcod_op_1clk_o  = 1'b0;
            dcod_rfa1_req_o = 1'b1;
            dcod_rfa2_req_o = op_fpxx_arith_l & dcod_insn_i[`OR1K_FPUOP_DOUBLE_BIT];
            if ((dcod_insn_i[2:0] == 3'd4) | (dcod_insn_i[2:0] == 3'd5)) begin // rD <- conv(rA)
              dcod_rfb1_req_o = 1'b0;
              dcod_rfb2_req_o = 1'b0;
            end
            else begin // rD <- rA op rB
              dcod_rfb1_req_o  = 1'b1;
              dcod_rfb2_req_o = op_fpxx_arith_l & dcod_insn_i[`OR1K_FPUOP_DOUBLE_BIT];
            end
            dcod_rfd1_wb_o = 1'b1;
          end
          else if (op_fp32_cmp_l | op_fp64_cmp_l) begin
            // SR[F] <- rA op rB
            dcod_op_1clk_o  = op_fp32_cmp_l;
            dcod_rfa1_req_o = 1'b1;
            dcod_rfb1_req_o = 1'b1;
            dcod_rfd1_wb_o  = 1'b0;
            // for FPU64
            dcod_rfa2_req_o = op_fp64_cmp_l;
            dcod_rfb2_req_o = op_fp64_cmp_l;
          end
          else begin
            // no legal FPU instruction
            dcod_op_1clk_o  = 1'b0;
            dcod_rfa1_req_o = 1'b0;
            dcod_rfb1_req_o = 1'b0;
            dcod_rfd1_wb_o  = 1'b0;
            // for FPU64
            dcod_rfa2_req_o = 1'b0;
            dcod_rfb2_req_o = 1'b0;
          end
        end // case or1k-opcode-fpu

      //`OR1K_OPCODE_MACRC, // Same to l.movhi - check!
      `OR1K_OPCODE_MACI,
      `OR1K_OPCODE_MAC:
        begin
          dcod_except_illegal_o = 1'b1;
          dcod_op_1clk_o        = 1'b0;
          dcod_op_pass_exec_o   = 1'b0;
          dcod_rfa1_req_o       = 1'b0;
          dcod_rfb1_req_o       = 1'b0;
          dcod_rfd1_wb_o        = 1'b0;
          // for FPU64
          dcod_rfa2_req_o       = 1'b0;
          dcod_rfb2_req_o       = 1'b0;
        end

      `OR1K_OPCODE_SHRTI:
        begin
          // synthesis parallel_case full_case
          case (dcod_insn_i[`OR1K_ALU_OPC_SECONDARY_SELECT])
            `OR1K_ALU_OPC_SECONDARY_SHRT_SLL, // rD <- SLLI(rA,Imm6)
            `OR1K_ALU_OPC_SECONDARY_SHRT_SRL, // rD <- SRLI(rA,Imm6)
            `OR1K_ALU_OPC_SECONDARY_SHRT_SRA, // rD <- SRAI(rA,Imm6)
            `OR1K_ALU_OPC_SECONDARY_SHRT_ROR: // rD <- RORI(rA,Imm6)
              begin
                dcod_except_illegal_o = 1'b0;
                dcod_op_1clk_o        = 1'b1;
                dcod_rfa1_req_o       = 1'b1;
                dcod_rfb1_req_o       = 1'b0;
                dcod_rfd1_wb_o        = 1'b1;
              end
            default:
              begin
                dcod_except_illegal_o = 1'b1;
                dcod_op_1clk_o        = 1'b0;
                dcod_rfa1_req_o       = 1'b0;
                dcod_rfb1_req_o       = 1'b0;
                dcod_rfd1_wb_o        = 1'b0;
              end
          endcase
          dcod_op_pass_exec_o = 1'b0;
          // for FPU64
          dcod_rfa2_req_o      = 1'b0;
          dcod_rfb2_req_o      = 1'b0;
        end

      `OR1K_OPCODE_ALU:
        begin
          // synthesis parallel_case full_case
          case (opc_alu)
            `OR1K_ALU_OPC_ADD,  // rD <- rA + rB
            `OR1K_ALU_OPC_ADDC, // rD <- rA + rB + carry
            `OR1K_ALU_OPC_SUB,  // rD <- rA - rB
            `OR1K_ALU_OPC_OR,   // rD <- rA | rB
            `OR1K_ALU_OPC_XOR,  // rD <- rA ^ rB
            `OR1K_ALU_OPC_AND,  // rD <- rA & rB
            `OR1K_ALU_OPC_CMOV, // rD <- flag ? rA : rB
            `OR1K_ALU_OPC_FFL1: // rD <- FFL1(rA)
              begin
                dcod_except_illegal_o = 1'b0;
                dcod_op_1clk_o        = 1'b1;
                dcod_op_pass_exec_o   = 1'b0;
                dcod_rfa1_req_o       = 1'b1;
                dcod_rfb1_req_o       = ~dcod_op_ffl1_o;
                dcod_rfd1_wb_o        = 1'b1;
              end

            `OR1K_ALU_OPC_DIV,  // rD <- rA / rB
            `OR1K_ALU_OPC_DIVU, // rD <- rA / rB
            `OR1K_ALU_OPC_MUL,  // rD <- rA * rB
            `OR1K_ALU_OPC_MULU: // rD <- rA * rB
              begin
                dcod_except_illegal_o = 1'b0;
                dcod_op_1clk_o        = 1'b0;
                dcod_op_pass_exec_o   = 1'b0;
                dcod_rfa1_req_o       = 1'b1;
                dcod_rfb1_req_o       = 1'b1;
                dcod_rfd1_wb_o        = 1'b1;
              end

            `OR1K_ALU_OPC_EXTBH,
            `OR1K_ALU_OPC_EXTW:
              begin
                dcod_except_illegal_o = 1'b1;
                dcod_op_1clk_o        = 1'b0;
                dcod_op_pass_exec_o   = 1'b0;
                dcod_rfa1_req_o       = 1'b0;
                dcod_rfb1_req_o       = 1'b0;
                dcod_rfd1_wb_o        = 1'b0;
              end

            `OR1K_ALU_OPC_SHRT:
              begin
                // synthesis parallel_case full_case
                case (dcod_insn_i[`OR1K_ALU_OPC_SECONDARY_SELECT])
                  `OR1K_ALU_OPC_SECONDARY_SHRT_SLL, // rD <- SLL(rA,rB)
                  `OR1K_ALU_OPC_SECONDARY_SHRT_SRL, // rD <- SRL(rA,rB)
                  `OR1K_ALU_OPC_SECONDARY_SHRT_SRA, // rD <- SRA(rA,rB)
                  `OR1K_ALU_OPC_SECONDARY_SHRT_ROR: // rD <- ROR(rA,rB)
                    begin
                      dcod_except_illegal_o = 1'b0;
                      dcod_op_1clk_o        = 1'b1;
                      dcod_rfa1_req_o       = 1'b1;
                      dcod_rfb1_req_o       = 1'b1;
                      dcod_rfd1_wb_o        = 1'b1;
                    end
                  default:
                    begin
                      dcod_except_illegal_o = 1'b1;
                      dcod_op_1clk_o        = 1'b0;
                      dcod_rfa1_req_o       = 1'b0;
                      dcod_rfb1_req_o       = 1'b0;
                      dcod_rfd1_wb_o        = 1'b0;
                    end
                endcase // case (dcod_insn_i[`OR1K_ALU_OPC_SECONDARY_SELECT])
                dcod_op_pass_exec_o = 1'b0;
              end

            default:
              begin
                dcod_except_illegal_o = 1'b1;
                dcod_op_1clk_o        = 1'b0;
                dcod_op_pass_exec_o   = 1'b0;
                dcod_rfa1_req_o       = 1'b0;
                dcod_rfb1_req_o       = 1'b0;
                dcod_rfd1_wb_o        = 1'b0;
              end
          endcase // alu_opc
          // for FPU64
          dcod_rfa2_req_o       = 1'b0;
          dcod_rfb2_req_o       = 1'b0;
        end // case or1k-opcode-alu

      `OR1K_OPCODE_SYSTRAPSYNC: begin
        if (dcod_insn_i[`OR1K_SYSTRAPSYNC_OPC_SELECT] == `OR1K_SYSTRAPSYNC_OPC_TRAP) begin
          dcod_except_illegal_o = 1'b0;
          dcod_op_pass_exec_o   = ~du_trap_enable_i;
        end
        else if ((dcod_insn_i[`OR1K_SYSTRAPSYNC_OPC_SELECT] == `OR1K_SYSTRAPSYNC_OPC_SYSCALL) |
                 ((dcod_insn_i[`OR1K_SYSTRAPSYNC_OPC_SELECT] == `OR1K_SYSTRAPSYNC_OPC_PSYNC) &
                  (FEATURE_PSYNC != "NONE")) |
                 ((dcod_insn_i[`OR1K_SYSTRAPSYNC_OPC_SELECT] == `OR1K_SYSTRAPSYNC_OPC_CSYNC) &
                  (FEATURE_CSYNC != "NONE")) |
                 (dcod_insn_i[`OR1K_SYSTRAPSYNC_OPC_SELECT] == `OR1K_SYSTRAPSYNC_OPC_MSYNC)) begin
          dcod_except_illegal_o = 1'b0;
          dcod_op_pass_exec_o   = 1'b0;
        end
        else begin
          dcod_except_illegal_o = 1'b1;
          dcod_op_pass_exec_o   = 1'b0;
        end
        dcod_op_1clk_o      = 1'b0;
        dcod_rfa1_req_o     = 1'b0;
        dcod_rfb1_req_o     = 1'b0;
        dcod_rfd1_wb_o      = 1'b0;
        // for FPU64
        dcod_rfa2_req_o       = 1'b0;
        dcod_rfb2_req_o       = 1'b0;
      end // case sys-trap-sync

      default:
        begin
          dcod_except_illegal_o = 1'b1;
          dcod_op_1clk_o        = 1'b0;
          dcod_op_pass_exec_o   = 1'b0;
          dcod_rfa1_req_o       = 1'b0;
          dcod_rfb1_req_o       = 1'b0;
          dcod_rfd1_wb_o        = 1'b0;
          // for FPU64
          dcod_rfa2_req_o       = 1'b0;
          dcod_rfb2_req_o       = 1'b0;
        end
    endcase // case (opc-insn)
  end // always


  // Calculate the link register result and
  // provide it as GPR[9] content for jump & link
  assign dcod_jal_result_o = (pc_decode_i + 8); // (FEATURE_DELAY_SLOT == "ENABLED")


  // Branch detection

  // jumps to register
  assign dcod_op_jr_o = (opc_insn == `OR1K_OPCODE_JR) |
                        (opc_insn == `OR1K_OPCODE_JALR);
  // jumps with link
  assign dcod_op_jal_o = (opc_insn == `OR1K_OPCODE_JALR) |
                         (opc_insn == `OR1K_OPCODE_JAL);

  // conditional branches
  wire dcod_op_bf  = (opc_insn == `OR1K_OPCODE_BF);
  wire dcod_op_bnf = (opc_insn == `OR1K_OPCODE_BNF);

  // do jumps or contitional branches to immediate
  //  # forwarded flag
  wire the_flag = exec_op_1clk_cmp_i ? exec_flag_set_i : ctrl_flag_i;
  //  # ---
  wire branch_to_imm = (opc_insn == `OR1K_OPCODE_J) | (opc_insn == `OR1K_OPCODE_JAL) |
                       (dcod_op_bf & the_flag) | (dcod_op_bnf & ~the_flag);

  wire [OPTION_OPERAND_WIDTH-1:0] branch_to_imm_target =
    pc_decode_i + {{4{dcod_insn_i[25]}},dcod_insn_i[25:16],dcod_imm16_o,2'b00};


  // detect jump/branch to indicate "delay slot" for next fetched instruction
  assign dcod_jump_or_branch_o = ((opc_insn < `OR1K_OPCODE_NOP) |   // l.j  | l.jal  | l.bnf | l.bf
                                  (opc_insn == `OR1K_OPCODE_JR) |   // l.jr
                                  (opc_insn == `OR1K_OPCODE_JALR)); // l.jalr
  // take branch flag / target / align exception
  //  # take branch flag
  assign dcod_do_branch_o          = branch_to_imm | dcod_op_jr_o;
  //  # take branch target
  assign dcod_do_branch_target_o   = branch_to_imm ? branch_to_imm_target : dcod_rfb1_i;
  //  # take branch align exception
  assign fetch_except_ibus_align_o = branch_to_imm ? (|branch_to_imm_target[1:0]) :
                                     dcod_op_jr_o  ? ((|dcod_rfb1_i[1:0]) & ~exe2dec_hazard_d1b1_i) :
                                                     1'b0;


  // Destination addresses
  assign dcod_rfd1_adr_o = dcod_op_jal_o ? 4'd9 : dcod_insn_i[`OR1K_RD_SELECT];


  // Which instructions writes comparison flag?
  assign dcod_flag_wb_o = dcod_op_setflag_o  |
                          dcod_op_fp32_cmp_o |
                          dcod_op_fp64_cmp_o |
                          (opc_insn == `OR1K_OPCODE_SWA);
  // Which instructions require comparison flag?
  //  # l.cmov
  assign dcod_flag_req_o = dcod_op_cmov_o;


  // Signals to stall FETCH if we are waiting flag
  //  # flag is going to be written by multi-cycle instruction
  //  # like 64-bit FPU comparison or l.swa
  assign dcod_flag_wb_mcycle_o = dcod_op_fp64_cmp_o | (opc_insn == `OR1K_OPCODE_SWA);
  //  # conditional branch
  assign dcod_op_brcond_o  = dcod_op_bf | dcod_op_bnf;


  // Which instruction writes carry flag?
  assign dcod_carry_wb_o = dcod_op_add_o | dcod_op_div_o;
  // Which instructions require carry flag?
  assign dcod_carry_req_o = dcod_adder_do_carry_o;

endmodule // mor1kx_decode_marocchino
