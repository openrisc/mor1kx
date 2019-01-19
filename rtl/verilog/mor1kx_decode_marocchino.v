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

module mor1kx_decode_marocchino
#(
  parameter OPTION_OPERAND_WIDTH = 32,
  parameter OPTION_RF_ADDR_WIDTH =  5,

  parameter FEATURE_PSYNC        = "NONE",
  parameter FEATURE_CSYNC        = "NONE"
)
(
  // clocks ans reset
  input                                 cpu_clk,

  // pipeline controls
  input                                 padv_dcod_i,
  input                                 padv_exec_i,
  input                                 pipeline_flush_i,

  // from IFETCH
  //  # instruction word valid flag
  input                                 fetch_valid_i,
  //  # an exception
  input                                 fetch_an_except_i,
  //  # instruction is in delay slot
  input                                 fetch_delay_slot_i,
  //  # instruction word itsef
  input          [`OR1K_INSN_WIDTH-1:0] fetch_insn_i,
  //  # operands addresses
  input      [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfa1_adr_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfb1_adr_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfa2_adr_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfb2_adr_i,
  //  # destiny addresses
  input      [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfd1_adr_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfd2_adr_i,

  // latched instruction word and it's attributes
  output reg                            dcod_empty_o,
  output reg                            dcod_delay_slot_o,

  // OMAN-to-DECODE hazards
  //  # relative operand A1
  output reg                            dcod_rfa1_req_o,
  output reg [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa1_adr_o,
  //  # relative operand B1
  output reg                            dcod_rfb1_req_o,
  output reg [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb1_adr_o,
  //  # relative operand A2
  output reg                            dcod_rfa2_req_o,
  output reg [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa2_adr_o,
  //  # relative operand B2
  output reg                            dcod_rfb2_req_o,
  output reg [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb2_adr_o,

  // destiny D1
  output reg [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfd1_adr_o, // address of Write-Back
  output reg                            dcod_rfd1_we_o,  // instruction performes Write-Back to D1
  // destiny D2 (for FPU64)
  output reg [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfd2_adr_o, // D2 address
  output reg                            dcod_rfd2_we_o, // instruction performes Write-Back to D2

  // instruction PC
  input      [OPTION_OPERAND_WIDTH-1:0] pc_fetch_i,
  output reg [OPTION_OPERAND_WIDTH-1:0] pc_decode_o,

  // IMM
  output reg [OPTION_OPERAND_WIDTH-1:0] dcod_immediate_o,
  output reg                            dcod_immediate_sel_o,

  // various instruction attributes
  output reg                            dcod_flag_we_o,   // instruction writes comparison flag

  // LSU related
  output reg      [`OR1K_IMM_WIDTH-1:0] dcod_imm16_o,
  output reg                            dcod_op_lsu_load_o,
  output reg                            dcod_op_lsu_store_o,
  output reg                            dcod_op_lsu_atomic_o,
  output reg                      [1:0] dcod_lsu_length_o,
  output reg                            dcod_lsu_zext_o,
  output reg                            dcod_op_msync_o,
  output reg                            dcod_op_lsu_any_o, // (load | store | l.msync)

  // Instructions which push EXECUTION without extra conditions
  output reg                            dcod_op_push_exec_o,
  // Instructions which push WRITE-BACK without extra conditions
  output reg                            dcod_op_push_wrbk_o,

  // 1-clock instruction
  output reg                            dcod_op_1clk_o,
  // Reqired flag or carry
  output reg                            dcod_flag_carry_req_o,
  // Adder related
  output reg                            dcod_op_add_o,
  output reg                            dcod_adder_do_sub_o,
  output reg                            dcod_adder_do_carry_o,
  // Shift
  output reg                            dcod_op_shift_o,
  output reg                      [3:0] dcod_opc_shift_o, // {SLL, SRL, SRA, ROR}
  // ffl1
  output reg                            dcod_op_ffl1_o,
  output reg                            dcod_opc_ffl1_o,
  // movhi, cmov
  output reg                            dcod_op_movhi_o,
  output reg                            dcod_op_cmov_o,
  // extsz
  output reg                            dcod_op_extsz_o,
  output reg                      [3:0] dcod_opc_extsz_o,
  // Logic
  output reg                            dcod_op_logic_o,
  output reg                      [3:0] dcod_lut_logic_o,
  // Jump & Link
  output reg                            dcod_op_jal_o,
  // Set flag related
  output reg                            dcod_op_setflag_o,
  output reg [`OR1K_COMP_OPC_WIDTH-1:0] dcod_opc_setflag_o,

  // Multiplier related
  output reg                            dcod_op_mul_o,

  // Divider related
  output reg                            dcod_op_div_o, // (not latched, to OMAN)
  output reg                            dcod_op_div_signed_o,
  output reg                            dcod_op_div_unsigned_o,

  // Combined for MULDIV_RSRVS
  output reg                            dcod_op_muldiv_o,

  // FPU3264 arithmetic part
  output reg                            dcod_op_fpxx_arith_o, // to OMAN and FPU3264_ARITH
  output reg                            dcod_op_fp64_arith_o, // to FPU3264_ARITH
  output reg                            dcod_op_fpxx_add_o, // to FPU3264_ARITH
  output reg                            dcod_op_fpxx_sub_o, // to FPU3264_ARITH
  output reg                            dcod_op_fpxx_mul_o, // to FPU3264_ARITH
  output reg                            dcod_op_fpxx_div_o, // to FPU3264_ARITH
  output reg                            dcod_op_fpxx_i2f_o, // to FPU3264_ARITH
  output reg                            dcod_op_fpxx_f2i_o, // to FPU3264_ARITH

  // FPU-64 comparison part
  output reg                            dcod_op_fpxx_cmp_o,
  output reg                      [2:0] dcod_opc_fpxx_cmp_o,

  // Combined for FPXX_RSRVS
  output reg                            dcod_op_fpxx_any_o,

  // MTSPR / MFSPR
  output reg                            dcod_op_mtspr_o,
  output reg                            dcod_op_mXspr_o, // (l.mfspr | l.mtspr)

  // Exceptions detected on decode stage flags
  //  ## enable l.trap exception
  input                                 du_trap_enable_i,
  //  ## outcome exception flags
  output reg                            dcod_except_illegal_o,
  output reg                            dcod_except_syscall_o,
  output reg                            dcod_except_trap_o,
  //  ## combined IFETCH/DECODE an exception flag
  output reg                            dcod_an_except_fd_o,

  // RFE
  output reg                            dcod_op_rfe_o
);

  wire [OPTION_OPERAND_WIDTH-1:0] imm_sext;
  wire                            imm_sext_sel;
  wire [OPTION_OPERAND_WIDTH-1:0] imm_zext;
  wire                            imm_zext_sel;
  wire [OPTION_OPERAND_WIDTH-1:0] imm_high;
  wire                            imm_high_sel;

  // Insn opcode
  wire [`OR1K_OPCODE_WIDTH-1:0]  opc_insn = fetch_insn_i[`OR1K_OPCODE_SELECT];


  //-----------------//
  // LSU instruction //
  //-----------------//


  // load opcodes are 6'b10_0000 to 6'b10_0110, 0 to 6, so check for 7 and up
  wire op_lsu_load = (opc_insn == `OR1K_OPCODE_LWA) |                                  // DECODE: l.lxx
                     (opc_insn == `OR1K_OPCODE_LWZ) | (opc_insn == `OR1K_OPCODE_LWS) | // DECODE: l.lxx
                     (opc_insn == `OR1K_OPCODE_LHZ) | (opc_insn == `OR1K_OPCODE_LHS) | // DECODE: l.lxx
                     (opc_insn == `OR1K_OPCODE_LBZ) | (opc_insn == `OR1K_OPCODE_LBS) | // DECODE: l.lxx
                     ((opc_insn == `OR1K_OPCODE_LD) & (OPTION_OPERAND_WIDTH == 64));   // DECODE: l.lxx

  // Detect when instruction is store
  wire op_lsu_store = (opc_insn == `OR1K_OPCODE_SWA) | (opc_insn == `OR1K_OPCODE_SW)  | // DECODE: l.sxx
                      (opc_insn == `OR1K_OPCODE_SH)  | (opc_insn == `OR1K_OPCODE_SB)  | // DECODE: l.sxx
                      ((opc_insn == `OR1K_OPCODE_SD) & (OPTION_OPERAND_WIDTH == 64));   // DECODE: l.sxx

  wire op_lsu_atomic = (opc_insn == `OR1K_OPCODE_LWA) | (opc_insn == `OR1K_OPCODE_SWA);


  // Decode length of load/store operation
  reg [1:0] lsu_length;
  // ---
  always @(opc_insn)
    // synthesis parallel_case
    case (opc_insn)
      // byte
      `OR1K_OPCODE_SB,
      `OR1K_OPCODE_LBZ,
      `OR1K_OPCODE_LBS: lsu_length = 2'b00;
      // half word
      `OR1K_OPCODE_SH,
      `OR1K_OPCODE_LHZ,
      `OR1K_OPCODE_LHS: lsu_length = 2'b01;
      // word
      `OR1K_OPCODE_SW,
      `OR1K_OPCODE_SWA,
      `OR1K_OPCODE_LWZ,
      `OR1K_OPCODE_LWS,
      `OR1K_OPCODE_LWA: lsu_length = 2'b10;
      // default
      default:          lsu_length = 2'b10;
  endcase

  wire lsu_zext = opc_insn[0];

  wire op_msync = (opc_insn == `OR1K_OPCODE_SYSTRAPSYNC) &
                   (fetch_insn_i[`OR1K_SYSTRAPSYNC_OPC_SELECT] ==
                    `OR1K_SYSTRAPSYNC_OPC_MSYNC);


  // --- l.nop ---
  wire op_nop = (opc_insn == `OR1K_OPCODE_NOP);


  // --- l.mf(t)spr ---
  wire op_mtspr = (opc_insn == `OR1K_OPCODE_MTSPR);
  wire op_mfspr = (opc_insn == `OR1K_OPCODE_MFSPR);


  // Detect when set SR[F] instruction
  wire op_setflag = (opc_insn == `OR1K_OPCODE_SF) |
                    (opc_insn == `OR1K_OPCODE_SFIMM);


  // jumps with link to 1-CLCK reservaton station for save GR[9]
  wire op_jal = (opc_insn == `OR1K_OPCODE_JALR) | (opc_insn == `OR1K_OPCODE_JAL);


  // --- integer ALU related ---
  wire [`OR1K_ALU_OPC_WIDTH-1:0] opc_alu  = fetch_insn_i[`OR1K_ALU_OPC_SELECT];
  wire op_alu = (opc_insn == `OR1K_OPCODE_ALU);


  // --- adder ---
  wire op_add = (op_alu &
                 ((opc_alu == `OR1K_ALU_OPC_ADDC) |
                  (opc_alu == `OR1K_ALU_OPC_ADD)  |
                  (opc_alu == `OR1K_ALU_OPC_SUB))) |
                (opc_insn == `OR1K_OPCODE_ADDIC)   |
                (opc_insn == `OR1K_OPCODE_ADDI)    |
                op_jal; // we use adder for l.jl/l.jalr to compute return address: (pc+8)
  // Adder control logic
  // Subtract when comparing to check if equal
  wire adder_do_sub = (op_alu & (opc_alu == `OR1K_ALU_OPC_SUB)) |
                      op_setflag;
  // Generate carry-in select
  wire adder_do_carry = (op_alu & (opc_alu == `OR1K_ALU_OPC_ADDC)) |
                        (opc_insn == `OR1K_OPCODE_ADDIC);


  // --- multiplier ---
  wire op_mul_signed   = (op_alu & (opc_alu == `OR1K_ALU_OPC_MUL)) |
                         (opc_insn == `OR1K_OPCODE_MULI);
  wire op_mul_unsigned = op_alu & (opc_alu == `OR1K_ALU_OPC_MULU);
  wire op_mul          = op_mul_signed | op_mul_unsigned;


  // --- divider ---
  wire op_div_signed   = op_alu & (opc_alu == `OR1K_ALU_OPC_DIV);
  wire op_div_unsigned = op_alu & (opc_alu == `OR1K_ALU_OPC_DIVU);
  wire op_div          = op_div_signed | op_div_unsigned;


  // --- shifter ---
  wire op_shift = (op_alu & (opc_alu  == `OR1K_ALU_OPC_SHRT)) |
                  (opc_insn == `OR1K_OPCODE_SHRTI);
  wire [`OR1K_ALU_OPC_SECONDARY_WIDTH-1:0] opc_shift;
  assign opc_shift = fetch_insn_i[`OR1K_ALU_OPC_SECONDARY_SELECT];


  // --- ffl1 ---
  wire op_ffl1  = op_alu & (opc_alu  == `OR1K_ALU_OPC_FFL1);
  wire opc_ffl1 = fetch_insn_i[8];


  // --- movhi / cmov ---
  wire op_movhi = (opc_insn == `OR1K_OPCODE_MOVHI);
  wire op_cmov  = (op_alu & (opc_alu == `OR1K_ALU_OPC_CMOV));


  // --- extsz ---
  // OPC is recoded to avoid aliasing of "word" and others
  wire is_extw  = (opc_alu == `OR1K_ALU_OPC_EXTW);
  wire op_extsz = op_alu & ((opc_alu == `OR1K_ALU_OPC_EXTBH) |
                            is_extw);
  wire [3:0] opc_extsz = {is_extw, fetch_insn_i[`OR1K_ALU_OPC_SECONDARY_SELECT]};


  // --- logic ---
  wire [3:0] lut_logic;
  assign lut_logic =
    ((op_alu & (opc_alu == `OR1K_ALU_OPC_OR )) | (opc_insn == `OR1K_OPCODE_ORI )) ? 4'b1110 :
   (((op_alu & (opc_alu == `OR1K_ALU_OPC_XOR)) | (opc_insn == `OR1K_OPCODE_XORI)) ? 4'b0110 :
   (((op_alu & (opc_alu == `OR1K_ALU_OPC_AND)) | (opc_insn == `OR1K_OPCODE_ANDI)) ? 4'b1000 :
                                                                                    4'b0000));


  // --- FPU3264 arithmetic part ---
  //  # tmp skeleton
  wire op_fpxx_arith_t = (~fetch_insn_i[3]) &        // arithmetic operation
                         (~(|fetch_insn_i[10:8]));   // all reserved bits are zeros
  //  # for further legality detection
  wire op_fpxx_arith_l = op_fpxx_arith_t & (fetch_insn_i[2:0] < 3'd6);
  //  # a legal FPU
  wire op_fpxx_arith = op_fpxx_arith_l & (opc_insn == `OR1K_OPCODE_FPU);
  //  # directly for FPU3264 execution unit
  wire op_fp64_arith = fetch_insn_i[`OR1K_FPUOP_DOUBLE_BIT];
  // fpu arithmetic opc:
  // ===================
  // 000 = add
  // 001 = substract
  // 010 = multiply
  // 011 = divide
  // 100 = i2f
  // 101 = f2i
  wire op_fpxx_add = op_fpxx_arith_t & (fetch_insn_i[2:0] == 3'd0) & (opc_insn == `OR1K_OPCODE_FPU);
  wire op_fpxx_sub = op_fpxx_arith_t & (fetch_insn_i[2:0] == 3'd1) & (opc_insn == `OR1K_OPCODE_FPU);
  wire op_fpxx_mul = op_fpxx_arith_t & (fetch_insn_i[2:0] == 3'd2) & (opc_insn == `OR1K_OPCODE_FPU);
  wire op_fpxx_div = op_fpxx_arith_t & (fetch_insn_i[2:0] == 3'd3) & (opc_insn == `OR1K_OPCODE_FPU);
  wire op_fpxx_i2f = op_fpxx_arith_t & (fetch_insn_i[2:0] == 3'd4) & (opc_insn == `OR1K_OPCODE_FPU);
  wire op_fpxx_f2i = op_fpxx_arith_t & (fetch_insn_i[2:0] == 3'd5) & (opc_insn == `OR1K_OPCODE_FPU);


  // --- FPU3264 comparison part ---
  //  # for further legality detection
  wire op_fpxx_cmp_l = fetch_insn_i[3] &          // comparison operation
                       (~(|fetch_insn_i[10:8])) & // all reserved bits are zeros
                       (fetch_insn_i[2:0] < 3'd6);
  //  # directly for FPU32 execution unit
  wire op_fpxx_cmp = op_fpxx_cmp_l & (opc_insn == `OR1K_OPCODE_FPU);
  // fpu comparison opc:
  // ===================
  // 000 = EQ
  // 001 = NE
  // 010 = GT
  // 011 = GE
  // 100 = LT
  // 101 = LE
  wire [2:0] opc_fpxx_cmp = fetch_insn_i[2:0];


  // Immediate for MF(T)SPR, LOADs and STOREs
  wire [`OR1K_IMM_WIDTH-1:0] imm16;
  assign imm16 = (op_mtspr | op_lsu_store) ?
                  {fetch_insn_i[25:21],fetch_insn_i[10:0]} :  // immediate for l.mtspr and l.s* (store)
                  fetch_insn_i[`OR1K_IMM_SELECT];             // immediate for l.mfspr and l.l* (load)

  // Immediate for arithmetic
  wire [`OR1K_IMM_WIDTH-1:0] opc_imm16 = fetch_insn_i[`OR1K_IMM_SELECT];

  //   Instructions with sign-extended immediate
  // excluding load/store, because LSU performs this extention by itself.
  assign imm_sext     = {{16{opc_imm16[15]}}, opc_imm16};
  assign imm_sext_sel = (opc_insn == `OR1K_OPCODE_ADDI)  |
                        (opc_insn == `OR1K_OPCODE_ADDIC) |
                        (opc_insn == `OR1K_OPCODE_XORI)  |
                        (opc_insn == `OR1K_OPCODE_MULI)  |
                        (opc_insn == `OR1K_OPCODE_SFIMM);

  //   Instructions with zero-extended immediate
  // excluding MT(F)SPR, because CTRL performs this extention by itself.
  assign imm_zext     = {16'd0, opc_imm16};
  assign imm_zext_sel = (opc_insn == `OR1K_OPCODE_ORI)  |
                        (opc_insn == `OR1K_OPCODE_ANDI) |
                        (opc_insn == `OR1K_OPCODE_SHRTI);

  // l.movhi
  assign imm_high     = {opc_imm16, 16'd0};
  assign imm_high_sel = op_movhi;

  // Use immediate flag and sign/zero extended Imm16
  wire [OPTION_OPERAND_WIDTH-1:0] immediate;
  assign immediate   = imm_sext_sel ? imm_sext :
                       imm_zext_sel ? imm_zext :
                                      imm_high;
  wire immediate_sel = imm_sext_sel | imm_zext_sel | imm_high_sel;


  // Exceptions and l.rfe
  wire op_rfe = (opc_insn == `OR1K_OPCODE_RFE);

  wire except_syscall = (opc_insn == `OR1K_OPCODE_SYSTRAPSYNC) &
                         (fetch_insn_i[`OR1K_SYSTRAPSYNC_OPC_SELECT] ==
                          `OR1K_SYSTRAPSYNC_OPC_SYSCALL);

  wire except_trap = (opc_insn == `OR1K_OPCODE_SYSTRAPSYNC) &
                      (fetch_insn_i[`OR1K_SYSTRAPSYNC_OPC_SELECT] ==
                       `OR1K_SYSTRAPSYNC_OPC_TRAP) & du_trap_enable_i;



  // various attributes
  reg attr_except_illegal;
  reg attr_op_1clk;
  reg attr_rfa1_req;
  reg attr_rfb1_req;
  reg attr_rfd1_we;
  reg attr_rfa2_req;
  reg attr_rfb2_req;
  // ---
  always @(*) begin
    // synthesis parallel_case
    case (opc_insn)
      `OR1K_OPCODE_J,     // pc <- pc + exts(Imm26 << 2)
      `OR1K_OPCODE_JAL,   // pc <- pc + exts(Imm26 << 2)
      `OR1K_OPCODE_JR,    // pc <- rB
      `OR1K_OPCODE_JALR,  // pc <- rB
      `OR1K_OPCODE_BNF,   // pc <- pc + exts(Imm26 << 2) if ~flag
      `OR1K_OPCODE_BF:    // pc <- pc + exts(Imm26 << 2) if flag
        begin
          attr_except_illegal = 1'b0;
          attr_op_1clk        = op_jal;  // compute GPR[9] by adder in 1CLK_EXEC
          attr_rfa1_req       = 1'b0;
          attr_rfb1_req       = 1'b0;    // l.jr/l.jalr are processed in OMAN in special way
          attr_rfd1_we        = op_jal;  // save GPR[9] by l.jal/l.jalr
          // for FPU64
          attr_rfa2_req       = 1'b0;
          attr_rfb2_req       = 1'b0;
        end

      `OR1K_OPCODE_MOVHI, // rD <- {Imm16,16'd0}
      `OR1K_OPCODE_RFE,
      `OR1K_OPCODE_NOP,
      `OR1K_OPCODE_CUST8:
        begin
          attr_except_illegal = 1'b0;
          attr_op_1clk        = op_movhi;
          attr_rfa1_req       = 1'b0;
          attr_rfb1_req       = 1'b0;
          attr_rfd1_we        = op_movhi;
          // for FPU64
          attr_rfa2_req       = 1'b0;
          attr_rfb2_req       = 1'b0;
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
          attr_except_illegal = 1'b0;
          attr_op_1clk        = (opc_insn != `OR1K_OPCODE_MULI);
          attr_rfa1_req       = 1'b1;
          attr_rfb1_req       = (opc_insn == `OR1K_OPCODE_SF);
          attr_rfd1_we        = (opc_insn != `OR1K_OPCODE_SF) & (opc_insn != `OR1K_OPCODE_SFIMM);
          // for FPU64
          attr_rfa2_req       = 1'b0;
          attr_rfb2_req       = 1'b0;
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
          attr_except_illegal = 1'b0;
          attr_op_1clk        = 1'b0;
          attr_rfa1_req       = 1'b1;
          attr_rfb1_req       = 1'b0;
          attr_rfd1_we        = 1'b1;
          // for FPU64
          attr_rfa2_req       = 1'b0;
          attr_rfb2_req       = 1'b0;
        end

      `OR1K_OPCODE_LD:  // rD <- MEM(rA + exts(Imm16))
         begin
          attr_except_illegal = (OPTION_OPERAND_WIDTH != 64);
          attr_op_1clk        = 1'b0;
          attr_rfa1_req       = (OPTION_OPERAND_WIDTH == 64);
          attr_rfb1_req       = 1'b0;
          attr_rfd1_we        = (OPTION_OPERAND_WIDTH == 64);
          // for FPU64
          attr_rfa2_req       = 1'b0;
          attr_rfb2_req       = 1'b0;
         end

      `OR1K_OPCODE_MTSPR, // rB -> SPR(rA | extz(Imm16))
      `OR1K_OPCODE_SW,    // rB -> MEM(rA + exts(Imm16))
      `OR1K_OPCODE_SB,    // rB -> MEM(rA + exts(Imm16))
      `OR1K_OPCODE_SH,    // rB -> MEM(rA + exts(Imm16))
      `OR1K_OPCODE_SWA:   // rB -> MEM(rA + exts(Imm16))
        begin
          attr_except_illegal = 1'b0;
          attr_op_1clk        = 1'b0;
          attr_rfa1_req       = 1'b1;
          attr_rfb1_req       = 1'b1;
          attr_rfd1_we        = 1'b0;
          // for FPU64
          attr_rfa2_req       = 1'b0;
          attr_rfb2_req       = 1'b0;
        end

      `OR1K_OPCODE_SD:  // rB -> MEM(rA + exts(Imm16))
        begin
          attr_except_illegal = (OPTION_OPERAND_WIDTH != 64);
          attr_op_1clk        = 1'b0;
          attr_rfa1_req       = (OPTION_OPERAND_WIDTH == 64);
          attr_rfb1_req       = (OPTION_OPERAND_WIDTH == 64);
          attr_rfd1_we        = 1'b0;
          // for FPU64
          attr_rfa2_req       = 1'b0;
          attr_rfb2_req       = 1'b0;
        end

      `OR1K_OPCODE_FPU:
        begin
          attr_except_illegal = ~(op_fpxx_arith_l | op_fpxx_cmp_l);
          attr_op_1clk        = 1'b0;
          if (op_fpxx_arith_l) begin
            attr_rfa1_req = 1'b1;
            attr_rfa2_req = op_fpxx_arith_l & fetch_insn_i[`OR1K_FPUOP_DOUBLE_BIT];
            if ((fetch_insn_i[2:0] == 3'd4) | (fetch_insn_i[2:0] == 3'd5)) begin // rD <- conv(rA)
              attr_rfb1_req = 1'b0;
              attr_rfb2_req = 1'b0;
            end
            else begin // rD <- rA op rB
              attr_rfb1_req  = 1'b1;
              attr_rfb2_req = op_fpxx_arith_l & fetch_insn_i[`OR1K_FPUOP_DOUBLE_BIT];
            end
            attr_rfd1_we = 1'b1;
          end
          else if (op_fpxx_cmp_l) begin
            // SR[F] <- rA op rB
            attr_rfa1_req = 1'b1;
            attr_rfb1_req = 1'b1;
            attr_rfd1_we  = 1'b0;
            // for FPU64
            attr_rfa2_req = fetch_insn_i[`OR1K_FPUOP_DOUBLE_BIT]; // SR[F] <- (rA compare rB)
            attr_rfb2_req = fetch_insn_i[`OR1K_FPUOP_DOUBLE_BIT]; // SR[F] <- (rA compare rB)
          end
          else begin
            // no legal FPU instruction
            attr_rfa1_req = 1'b0;
            attr_rfb1_req = 1'b0;
            attr_rfd1_we  = 1'b0;
            // for FPU64
            attr_rfa2_req = 1'b0;
            attr_rfb2_req = 1'b0;
          end
        end // case or1k-opcode-fpu

      `OR1K_OPCODE_SHRTI:
        begin
          // synthesis parallel_case
          case (opc_shift)
            `OR1K_ALU_OPC_SECONDARY_SHRT_SLL, // rD <- SLLI(rA,Imm6)
            `OR1K_ALU_OPC_SECONDARY_SHRT_SRL, // rD <- SRLI(rA,Imm6)
            `OR1K_ALU_OPC_SECONDARY_SHRT_SRA, // rD <- SRAI(rA,Imm6)
            `OR1K_ALU_OPC_SECONDARY_SHRT_ROR: // rD <- RORI(rA,Imm6)
              begin
                attr_except_illegal = 1'b0;
                attr_op_1clk        = 1'b1;
                attr_rfa1_req       = 1'b1;
                attr_rfb1_req       = 1'b0;
                attr_rfd1_we        = 1'b1;
              end
            default:
              begin
                attr_except_illegal = 1'b1;
                attr_op_1clk        = 1'b0;
                attr_rfa1_req       = 1'b0;
                attr_rfb1_req       = 1'b0;
                attr_rfd1_we        = 1'b0;
              end
          endcase
          // for FPU64
          attr_rfa2_req      = 1'b0;
          attr_rfb2_req      = 1'b0;
        end

      `OR1K_OPCODE_ALU:
        begin
          // synthesis parallel_case
          case (opc_alu)
            `OR1K_ALU_OPC_EXTBH, // rD <- zero/sign extention (rA) for 8- and 16- bits
            `OR1K_ALU_OPC_EXTW,  // rD <- rA for 32-bits
            `OR1K_ALU_OPC_FFL1:  // rD <- FFL1(rA)
              begin
                attr_except_illegal = (OPTION_OPERAND_WIDTH == 64); // extsz/ffl are not implemented for ORBIS64
                attr_op_1clk        = 1'b1;
                attr_rfa1_req       = 1'b1;
                attr_rfb1_req       = 1'b0;
                attr_rfd1_we        = 1'b1;
              end

            `OR1K_ALU_OPC_ADD,  // rD <- rA + rB
            `OR1K_ALU_OPC_ADDC, // rD <- rA + rB + carry
            `OR1K_ALU_OPC_SUB,  // rD <- rA - rB
            `OR1K_ALU_OPC_OR,   // rD <- rA | rB
            `OR1K_ALU_OPC_XOR,  // rD <- rA ^ rB
            `OR1K_ALU_OPC_AND,  // rD <- rA & rB
            `OR1K_ALU_OPC_CMOV: // rD <- flag ? rA : rB
              begin
                attr_except_illegal = 1'b0;
                attr_op_1clk        = 1'b1;
                attr_rfa1_req       = 1'b1;
                attr_rfb1_req       = 1'b1;
                attr_rfd1_we        = 1'b1;
              end

            `OR1K_ALU_OPC_DIV,  // rD <- rA / rB
            `OR1K_ALU_OPC_DIVU, // rD <- rA / rB
            `OR1K_ALU_OPC_MUL,  // rD <- rA * rB
            `OR1K_ALU_OPC_MULU: // rD <- rA * rB
              begin
                attr_except_illegal = 1'b0;
                attr_op_1clk        = 1'b0;
                attr_rfa1_req       = 1'b1;
                attr_rfb1_req       = 1'b1;
                attr_rfd1_we        = 1'b1;
              end

            `OR1K_ALU_OPC_SHRT:
              begin
                // synthesis parallel_case
                case (opc_shift)
                  `OR1K_ALU_OPC_SECONDARY_SHRT_SLL, // rD <- SLL(rA,rB)
                  `OR1K_ALU_OPC_SECONDARY_SHRT_SRL, // rD <- SRL(rA,rB)
                  `OR1K_ALU_OPC_SECONDARY_SHRT_SRA, // rD <- SRA(rA,rB)
                  `OR1K_ALU_OPC_SECONDARY_SHRT_ROR: // rD <- ROR(rA,rB)
                    begin
                      attr_except_illegal = 1'b0;
                      attr_op_1clk        = 1'b1;
                      attr_rfa1_req       = 1'b1;
                      attr_rfb1_req       = 1'b1;
                      attr_rfd1_we        = 1'b1;
                    end
                  default:
                    begin
                      attr_except_illegal = 1'b1;
                      attr_op_1clk        = 1'b0;
                      attr_rfa1_req       = 1'b0;
                      attr_rfb1_req       = 1'b0;
                      attr_rfd1_we        = 1'b0;
                    end
                endcase
              end

            default:
              begin
                attr_except_illegal = 1'b1;
                attr_op_1clk        = 1'b0;
                attr_rfa1_req       = 1'b0;
                attr_rfb1_req       = 1'b0;
                attr_rfd1_we        = 1'b0;
              end
          endcase // alu-opc
          // for FPU64
          attr_rfa2_req       = 1'b0;
          attr_rfb2_req       = 1'b0;
        end // case or1k-opcode-alu

      `OR1K_OPCODE_SYSTRAPSYNC: begin
        // synthesis parallel_case
        case (fetch_insn_i[`OR1K_SYSTRAPSYNC_OPC_SELECT])
          `OR1K_SYSTRAPSYNC_OPC_TRAP,
          `OR1K_SYSTRAPSYNC_OPC_SYSCALL:
            begin
              attr_except_illegal = 1'b0;
            end
          `OR1K_SYSTRAPSYNC_OPC_MSYNC:
            begin
              attr_except_illegal = 1'b0;
            end
          `OR1K_SYSTRAPSYNC_OPC_PSYNC:
            begin
              attr_except_illegal = 1'b1; // (FEATURE_PSYNC == "NONE"); - not implemented
            end
          `OR1K_SYSTRAPSYNC_OPC_CSYNC:
            begin
              attr_except_illegal = 1'b1; // (FEATURE_CSYNC == "NONE"); - not implemented
            end
          default:
            begin
              attr_except_illegal = 1'b1;
            end
        endcase
        attr_op_1clk      = 1'b0;
        attr_rfa1_req     = 1'b0;
        attr_rfb1_req     = 1'b0;
        attr_rfd1_we      = 1'b0;
        // for FPU64
        attr_rfa2_req     = 1'b0;
        attr_rfb2_req     = 1'b0;
      end // case sys-trap-sync

      default:
        begin
          attr_except_illegal = 1'b1;
          attr_op_1clk        = 1'b0;
          attr_rfa1_req       = 1'b0;
          attr_rfb1_req       = 1'b0;
          attr_rfd1_we        = 1'b0;
          // for FPU64
          attr_rfa2_req       = 1'b0;
          attr_rfb2_req       = 1'b0;
        end
    endcase // case (opc-insn)
  end // always


  // Destination addresses:
  //  ## for l.jal/l.jalr
  localparam [(OPTION_RF_ADDR_WIDTH-1):0]  JAL_RFD1_ADR =  9;
  localparam [(OPTION_RF_ADDR_WIDTH-1):0]  JAL_RFD2_ADR = 10;
  //  ## reset / flush
  localparam [(OPTION_RF_ADDR_WIDTH-1):0]  RST_RFD2_ADR =  1;


  //--------------------------//
  // IFETCH -> DECODE latches //
  //--------------------------//

  // Notes about instructions which push EXECUTION / WRITE-BACK without extra conditions
  //  # l.msync - locks LSU, but takes slot in OMAN to pushing Write-Back
  //  # l.jal / l.jalr - go through 1-CLK
  wire op_jb_push_exec = (opc_insn == `OR1K_OPCODE_J)  | (opc_insn == `OR1K_OPCODE_JR) | // J/B PUSH EXECUTE
                         (opc_insn == `OR1K_OPCODE_BF) | (opc_insn == `OR1K_OPCODE_BNF); // J/B PUSH EXECUTE

  // Combined IFETCH/DECODE exceptions flag
  wire an_except_fd = fetch_an_except_i   |                               // AN EXCEPT F/D
                      attr_except_illegal | except_syscall | except_trap; // AN EXCEPT F/D

  // signals which affect pipeline control (see OMAN)
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i) begin
      dcod_empty_o        <= 1'b1;
      dcod_op_1clk_o      <= 1'b0;
      dcod_op_muldiv_o    <= 1'b0;
      dcod_op_fpxx_any_o  <= 1'b0;
      dcod_op_lsu_any_o   <= 1'b0;
      dcod_op_mXspr_o     <= 1'b0;
      dcod_op_push_exec_o <= 1'b0;
      dcod_op_push_wrbk_o <= 1'b0;
      // for correct tracking data dependacy
      dcod_rfd1_we_o      <= 1'b0;
      dcod_rfd2_we_o      <= 1'b0;
      dcod_flag_we_o      <= 1'b0;
    end
    else if (padv_dcod_i) begin
      dcod_empty_o        <= (~fetch_valid_i);
      dcod_op_1clk_o      <= attr_op_1clk;
      dcod_op_muldiv_o    <= op_mul | op_div;
      dcod_op_fpxx_any_o  <= op_fpxx_arith | op_fpxx_cmp;
      dcod_op_lsu_any_o   <= op_lsu_load | op_lsu_store | op_msync;
      dcod_op_mXspr_o     <= op_mfspr | op_mtspr;
      dcod_op_push_exec_o <= an_except_fd | op_nop | op_rfe | op_jb_push_exec;
      dcod_op_push_wrbk_o <= an_except_fd | op_nop | op_rfe | op_msync;
      // for correct tracking data dependacy
      dcod_rfd1_we_o      <= attr_rfd1_we;
      dcod_rfd2_we_o      <= op_fpxx_arith & op_fp64_arith;
      dcod_flag_we_o      <= op_setflag | op_fpxx_cmp | (opc_insn == `OR1K_OPCODE_SWA);
    end
    else if (padv_exec_i) begin
      dcod_empty_o        <= 1'b1;
      dcod_op_1clk_o      <= 1'b0;
      dcod_op_muldiv_o    <= 1'b0;
      dcod_op_fpxx_any_o  <= 1'b0;
      dcod_op_lsu_any_o   <= 1'b0;
      dcod_op_mXspr_o     <= 1'b0;
      dcod_op_push_exec_o <= 1'b0;
      dcod_op_push_wrbk_o <= 1'b0;
      // for correct tracking data dependacy
      dcod_rfd1_we_o      <= 1'b0;
      dcod_rfd2_we_o      <= 1'b0;
      dcod_flag_we_o      <= 1'b0;
    end
  end // at clock

  // signals which don't affect pipeline control
  always @(posedge cpu_clk) begin
    if (padv_dcod_i) begin
      dcod_delay_slot_o         <= fetch_delay_slot_i;
      // destiny D1
      dcod_rfd1_adr_o           <= op_jal ? JAL_RFD1_ADR : fetch_rfd1_adr_i;
      // destiny D2 (for FPU64)
      dcod_rfd2_adr_o           <= op_jal ? JAL_RFD2_ADR : fetch_rfd2_adr_i;
      // IMM
      dcod_immediate_o          <= immediate;
      dcod_immediate_sel_o      <= immediate_sel;
      // LSU related
      dcod_imm16_o              <= imm16;
      dcod_op_lsu_load_o        <= op_lsu_load;
      dcod_op_lsu_store_o       <= op_lsu_store;
      dcod_op_lsu_atomic_o      <= op_lsu_atomic;
      dcod_lsu_length_o         <= lsu_length;
      dcod_lsu_zext_o           <= lsu_zext;
      dcod_op_msync_o           <= op_msync;
      // Reqired flag or carry
      dcod_flag_carry_req_o     <= op_cmov | adder_do_carry;
      // Adder related
      dcod_op_add_o             <= op_add;
      dcod_adder_do_sub_o       <= adder_do_sub;
      dcod_adder_do_carry_o     <= adder_do_carry;
      // Shift
      dcod_op_shift_o           <= op_shift;
      dcod_opc_shift_o          <= {(opc_shift == `OR1K_ALU_OPC_SECONDARY_SHRT_SLL),
                                    (opc_shift == `OR1K_ALU_OPC_SECONDARY_SHRT_SRL),
                                    (opc_shift == `OR1K_ALU_OPC_SECONDARY_SHRT_SRA),
                                    (opc_shift == `OR1K_ALU_OPC_SECONDARY_SHRT_ROR)};
      // ffl
      dcod_op_ffl1_o            <= op_ffl1;
      dcod_opc_ffl1_o           <= opc_ffl1;
      // movhi, cmov
      dcod_op_movhi_o           <= op_movhi;
      dcod_op_cmov_o            <= op_cmov;
      // extsz
      dcod_op_extsz_o           <= op_extsz;
      dcod_opc_extsz_o          <= opc_extsz;
      // Logic
      dcod_op_logic_o           <= |lut_logic;
      dcod_lut_logic_o          <= lut_logic;
      // Jump & Link
      dcod_op_jal_o             <= op_jal;
      // Set flag related
      dcod_op_setflag_o         <= op_setflag;
      dcod_opc_setflag_o        <= fetch_insn_i[`OR1K_COMP_OPC_SELECT];
      // Multiplier related
      dcod_op_mul_o             <= op_mul;
      // Divider related
      dcod_op_div_o             <= op_div;
      dcod_op_div_signed_o      <= op_div_signed;
      dcod_op_div_unsigned_o    <= op_div_unsigned;
      // FPU3264 arithmetic part
      dcod_op_fpxx_arith_o      <= op_fpxx_arith;
      dcod_op_fp64_arith_o      <= op_fp64_arith;
      dcod_op_fpxx_add_o        <= op_fpxx_add;
      dcod_op_fpxx_sub_o        <= op_fpxx_sub;
      dcod_op_fpxx_mul_o        <= op_fpxx_mul;
      dcod_op_fpxx_div_o        <= op_fpxx_div;
      dcod_op_fpxx_i2f_o        <= op_fpxx_i2f;
      dcod_op_fpxx_f2i_o        <= op_fpxx_f2i;
      // FPU-64 comparison part
      dcod_op_fpxx_cmp_o        <= op_fpxx_cmp;
      dcod_opc_fpxx_cmp_o       <= opc_fpxx_cmp;
      // MTSPR / MFSPR
      dcod_op_mtspr_o           <= op_mtspr;
      // outcome exception flags
      dcod_except_illegal_o     <= attr_except_illegal;
      dcod_except_syscall_o     <= except_syscall;
      dcod_except_trap_o        <= except_trap;
      // combined IFETCH/DECODE an exception flag
      dcod_an_except_fd_o       <= an_except_fd;
      // RFE
      dcod_op_rfe_o             <= op_rfe;
       // INSN PC
      pc_decode_o               <= pc_fetch_i;
    end
  end // @cpu-clk

  // requested operands flags in DECODE
  always @(posedge cpu_clk) begin
    if (padv_dcod_i) begin
      dcod_rfa1_req_o <= attr_rfa1_req;
      dcod_rfb1_req_o <= attr_rfb1_req;
      dcod_rfa2_req_o <= attr_rfa2_req;
      dcod_rfb2_req_o <= attr_rfb2_req;
    end
    else if (padv_exec_i) begin
      dcod_rfa1_req_o <= 1'b0;
      dcod_rfb1_req_o <= 1'b0;
      dcod_rfa2_req_o <= 1'b0;
      dcod_rfb2_req_o <= 1'b0;
    end
  end // at cpu clock

  // requested operands addresses in DECODE
  always @(posedge cpu_clk) begin
    if (padv_dcod_i) begin
      dcod_rfa1_adr_o <= fetch_rfa1_adr_i;
      dcod_rfb1_adr_o <= fetch_rfb1_adr_i;
      dcod_rfa2_adr_o <= fetch_rfa2_adr_i;
      dcod_rfb2_adr_o <= fetch_rfb2_adr_i;
    end
  end // at cpu clock

endmodule // mor1kx_decode_marocchino
