/* ****************************************************************************
  This Source Code Form is subject to the terms of the
  Open Hardware Description License, v. 1.0. If a copy
  of the OHDL was not distributed with this file, You
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: mor1kx execute stage for MAROCCHINO pipeline

  Derived from mor1kx_execute_alu and mor1kx_execute_ctrl_cappuccino

  Copyright (C) 2012 Julius Baxter <juliusbaxter@gmail.com>
  Copyright (C) 2012-2014 Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>
  Copyright (C) 2015 Andrey Bacherov <avbacherov@opencores.org>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_execute_marocchino
#(
  parameter OPTION_OPERAND_WIDTH = 32,
  parameter OPTION_RF_ADDR_WIDTH =  5,

  parameter FEATURE_OVERFLOW   = "NONE",
  parameter FEATURE_CARRY_FLAG = "ENABLED",

  parameter FEATURE_EXT = "NONE",

  parameter FEATURE_FPU = "NONE" // ENABLED|NONE
)
(
  // clocks and resets
  input               clk,
  input               rst,

  // pipeline control signal in
  input               padv_decode_i,
  input               padv_wb_i,
  input               pipeline_flush_i,// flush pipelined fpu

  // input data
  input [OPTION_OPERAND_WIDTH-1:0]  rfa_i,
  input [OPTION_OPERAND_WIDTH-1:0]  rfb_i,
  input [OPTION_OPERAND_WIDTH-1:0]  immediate_i,
  input                             immediate_sel_i,

  // opcode for alu
  input                             op_alu_i,
  input [`OR1K_ALU_OPC_WIDTH-1:0]   opc_alu_i,
  input [`OR1K_ALU_OPC_WIDTH-1:0]   opc_alu_secondary_i,

  // adder's inputs
  input                             op_add_i,
  input                             adder_do_sub_i,
  input                             adder_do_carry_i,
  // adder's outputs
  output [OPTION_OPERAND_WIDTH-1:0] exec_lsu_adr_o,

  // multiplier inputs
  input               op_mul_i,

  // dividion inputs
  input               op_div_i,
  input               op_div_signed_i,
  input               op_div_unsigned_i,

  // shift, ffl1, movhi
  input               op_shift_i,
  input               op_ffl1_i,
  input               op_movhi_i,

  // ALU result forming
  input                                 op_jal_i,
  input      [OPTION_OPERAND_WIDTH-1:0] exec_jal_result_i,
  output     [OPTION_OPERAND_WIDTH-1:0] alu_nl_result_o, // nl: not latched

  // FPU related
  input      [`OR1K_FPUOP_WIDTH-1:0]   op_fpu_i,
  input      [`OR1K_FPCSR_RM_SIZE-1:0] fpu_round_mode_i,
  output     [`OR1K_FPCSR_WIDTH-1:0]   exec_fpcsr_o,
  output                               exec_fpcsr_set_o,

  // flag related inputs
  input op_setflag_i,
  input flag_i, // fed back from ctrl (for cmov)
  // flag related outputs
  output exec_flag_set_o,
  output exec_flag_clear_o,

  // carry related inputs
  input carry_i,
  // carry related outputs
  output exec_carry_set_o,
  output exec_carry_clear_o,

  // owerflow related outputs
  output exec_overflow_set_o,
  output exec_overflow_clear_o,

  // MTSPR & MFSPR related inputs
  input op_mtspr_i,
  input op_mfspr_i,
  input ctrl_mfspr_ack_i,
  input ctrl_mtspr_ack_i,

  // MSYNC related controls
  input      op_msync_i,
  input      msync_done_i,

  // LSU related inputs
  input       op_lsu_load_i,
  input       op_lsu_store_i,
  input       lsu_valid_i,
  input       lsu_excepts_i,

  // ready flags
  output exec_valid_o
);

  localparam  EXEDW = OPTION_OPERAND_WIDTH; // short name



  wire [EXEDW-1:0] a = rfa_i;
  wire [EXEDW-1:0] b = immediate_sel_i ? immediate_i : rfb_i;



  //-----------------
  // Adder/subtractor
  //-----------------
  // outputs
  wire             adder_carryout;
  wire [EXEDW-1:0] adder_result;
  // inputs
  wire [EXEDW-1:0] b_neg = ~b;
  wire [EXEDW-1:0] b_mux = adder_do_sub_i ? b_neg : b;
  wire carry_in = adder_do_sub_i | (adder_do_carry_i & carry_i);
  // Adder
  assign {adder_carryout, adder_result} =
            a + b_mux + {{(EXEDW-1){1'b0}},carry_in};
  // result sign
  wire adder_result_sign = adder_result[EXEDW-1];
  // signed overflow detection
  // Input signs are same and result sign is different to input signs
  wire adder_signed_overflow =
            (a[EXEDW-1] == b_mux[EXEDW-1]) &
            (a[EXEDW-1] ^ adder_result[EXEDW-1]);
  // unsigned overflow detection
  wire adder_unsigned_overflow = adder_carryout;



  //-----------------
  // Comparison logic
  //-----------------
  wire a_eq_b = (a == b);// Equal compare
  wire a_lts_b = ~(adder_result_sign == adder_signed_overflow);// Signed compare
  wire a_ltu_b = ~adder_carryout;// Unsigned compare
  // comb.
  reg flag_set;
  always @*
    case(opc_alu_secondary_i)
      `OR1K_COMP_OPC_EQ:  flag_set = a_eq_b;
      `OR1K_COMP_OPC_NE:  flag_set = ~a_eq_b;
      `OR1K_COMP_OPC_GTU: flag_set = ~(a_eq_b | a_ltu_b);
      `OR1K_COMP_OPC_GTS: flag_set = ~(a_eq_b | a_lts_b);
      `OR1K_COMP_OPC_GEU: flag_set = ~a_ltu_b;
      `OR1K_COMP_OPC_GES: flag_set = ~a_lts_b;
      `OR1K_COMP_OPC_LTU: flag_set = a_ltu_b;
      `OR1K_COMP_OPC_LTS: flag_set = a_lts_b;
      `OR1K_COMP_OPC_LEU: flag_set = a_eq_b | a_ltu_b;
      `OR1K_COMP_OPC_LES: flag_set = a_eq_b | a_lts_b;
      default:            flag_set = 1'b0;
    endcase



  //--------------------------------------------
  // 32-bit multiplier
  //--------------------------------------------
  reg [EXEDW-1:0] mul_opa;
  reg [EXEDW-1:0] mul_opb;
  reg [EXEDW-1:0] mul_result1;
  reg [EXEDW-1:0] mul_result;
  reg       [2:0] mul_cnt_shr;
  wire            mul_valid;
  // multiplier
  always @(posedge clk) begin
    if (op_mul_i) begin
      mul_opa <= a;
      mul_opb <= b;
    end
    mul_result1 <= mul_opa * mul_opb;
    mul_result  <= mul_result1;
  end // @clock
  // multiplier's clock counter
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      mul_cnt_shr <= 3'd0;
    else if (padv_decode_i | pipeline_flush_i) // reset @ new decode data
      mul_cnt_shr <= 3'd0;
    else if (~(|mul_cnt_shr))
      mul_cnt_shr <= {2'd0,op_mul_i}; // init
    else if (~mul_valid)
      mul_cnt_shr <= {mul_cnt_shr[1:0], 1'b0};
  end // @clock
  //  multiplier's ready flag
  assign mul_valid = mul_cnt_shr[2];



  //--------------------------------------------
  // 32-bit divider
  //--------------------------------------------
  reg [5:0] div_count;
  reg [EXEDW-1:0] div_n;
  reg [EXEDW-1:0] div_d;
  reg [EXEDW-1:0] div_r;
  wire [EXEDW:0]  div_sub;
  reg             div_neg;
  reg             div_done;
  reg             div_by_zero_r;


  assign div_sub = {div_r[EXEDW-2:0],div_n[EXEDW-1]} - div_d;

  // Cycle counter
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      div_done  <= 1'b0;
      div_count <= 6'd0;
    end
    if (padv_decode_i | pipeline_flush_i) begin // reset @ new decode data
      div_done  <= 1'b0;
      div_count <= 6'd0;
    end
    else if (op_div_i & (~(|div_count))) begin
      div_done  <= 1'b0;
      div_count <= EXEDW;
    end
    else if (div_count == 6'd1)
      div_done <= 1'b1;
    else if (~div_done)
      div_count <= div_count - 6'd1;
  end // @clock

  always @(posedge clk) begin
    if (op_div_i & (~(|div_count))) begin
      div_n <= rfa_i;
      div_d <= rfb_i;
      div_r <= 0;
      div_neg <= 1'b0;
      div_by_zero_r <= ~(|rfb_i);
      /*
       * Convert negative operands in the case of signed division.
       * If only one of the operands is negative, the result is
       * converted back to negative later on
       */
      if (op_div_signed_i) begin
        if (rfa_i[EXEDW-1] ^ rfb_i[EXEDW-1])
          div_neg <= 1'b1;

        if (rfa_i[EXEDW-1])
          div_n <= ~rfa_i + 1;

        if (rfb_i[EXEDW-1])
          div_d <= ~rfb_i + 1;
      end
    end
    else if (~div_done) begin
      if (~div_sub[EXEDW]) begin // div_sub >= 0
        div_r <= div_sub[EXEDW-1:0];
        div_n <= {div_n[EXEDW-2:0], 1'b1};
      end else begin // div_sub < 0
        div_r <= {div_r[EXEDW-2:0],div_n[EXEDW-1]};
        div_n <= {div_n[EXEDW-2:0], 1'b0};
      end
    end // ~done
  end // @clock

  wire div_valid   = div_done;
  wire div_by_zero = div_by_zero_r;
  wire [EXEDW-1:0] div_result = div_neg ? ~div_n + 1 : div_n;



  //------------
  // FPU related
  //------------
  //  arithmetic part interface
  wire fpu_op_is_arith;
  wire fpu_arith_valid;
  wire [EXEDW-1:0] fpu_result;
  //  comparator part interface
  wire fpu_op_is_cmp;
  wire fpu_cmp_valid;
  wire fpu_cmp_flag;
  //  instance
  generate
    /* verilator lint_off WIDTH */
    if (FEATURE_FPU!="NONE") begin :  fpu_alu_ena
    /* verilator lint_on WIDTH */
      wire [(`OR1K_FPCSR_WIDTH-1):0] fpcsr_w;
      // fpu32 instance
      pfpu32_top u_pfpu32
      (
        .clk(clk),
        .rst(rst),
        .flush_i(pipeline_flush_i),
        .padv_decode_i(padv_decode_i),
        .padv_execute_i(padv_wb_i),
        .op_fpu_i(op_fpu_i),
        .round_mode_i(fpu_round_mode_i),
        .rfa_i(rfa_i),
        .rfb_i(rfb_i),
        .fpu_result_o(fpu_result),
        .fpu_arith_valid_o(fpu_arith_valid),
        .fpu_cmp_flag_o(fpu_cmp_flag),
        .fpu_cmp_valid_o(fpu_cmp_valid),
        .fpcsr_o(fpcsr_w)
      );
      // some glue logic
      assign fpu_op_is_arith = op_fpu_i[`OR1K_FPUOP_WIDTH-1] & (~op_fpu_i[3]);
      assign fpu_op_is_cmp   = op_fpu_i[`OR1K_FPUOP_WIDTH-1] &   op_fpu_i[3];
      // flag to update FPCSR
      assign exec_fpcsr_o     = fpcsr_w;
      assign exec_fpcsr_set_o = (fpu_arith_valid | fpu_cmp_valid);
    end
    else begin :  fpu_alu_none
      // arithmetic part
      assign fpu_op_is_arith = 1'b0;
      assign fpu_arith_valid = 1'b0;
      assign fpu_result      = {EXEDW{1'b0}};
      // comparator part
      assign fpu_op_is_cmp = 1'b0;
      assign fpu_cmp_valid = 1'b0;
      assign fpu_cmp_flag  = 1'b0;
      // fpu's common
      assign exec_fpcsr_o     = {`OR1K_FPCSR_WIDTH{1'b0}};
      assign exec_fpcsr_set_o = 1'b0;
    end // fpu_ena/fpu_none
  endgenerate // FPU related


  //------------
  // FFL1
  //------------
  wire [EXEDW-1:0] ffl1_result;
  assign ffl1_result = (opc_alu_secondary_i[2]) ?
               (a[31] ? 32 : a[30] ? 31 : a[29] ? 30 :
                a[28] ? 29 : a[27] ? 28 : a[26] ? 27 :
                a[25] ? 26 : a[24] ? 25 : a[23] ? 24 :
                a[22] ? 23 : a[21] ? 22 : a[20] ? 21 :
                a[19] ? 20 : a[18] ? 19 : a[17] ? 18 :
                a[16] ? 17 : a[15] ? 16 : a[14] ? 15 :
                a[13] ? 14 : a[12] ? 13 : a[11] ? 12 :
                a[10] ? 11 : a[9] ? 10 : a[8] ? 9 :
                a[7] ? 8 : a[6] ? 7 : a[5] ? 6 : a[4] ? 5 :
                a[3] ? 4 : a[2] ? 3 : a[1] ? 2 : a[0] ? 1 : 0 ) :
               (a[0] ? 1 : a[1] ? 2 : a[2] ? 3 : a[3] ? 4 :
                a[4] ? 5 : a[5] ? 6 : a[6] ? 7 : a[7] ? 8 :
                a[8] ? 9 : a[9] ? 10 : a[10] ? 11 : a[11] ? 12 :
                a[12] ? 13 : a[13] ? 14 : a[14] ? 15 :
                a[15] ? 16 : a[16] ? 17 : a[17] ? 18 :
                a[18] ? 19 : a[19] ? 20 : a[20] ? 21 :
                a[21] ? 22 : a[22] ? 23 : a[23] ? 24 :
                a[24] ? 25 : a[25] ? 26 : a[26] ? 27 :
                a[27] ? 28 : a[28] ? 29 : a[29] ? 30 :
                a[30] ? 31 : a[31] ? 32 : 0);



  //---------------
  // Barrel shifter
  //---------------
  // Shifter wires
  wire [`OR1K_ALU_OPC_SECONDARY_WIDTH-1:0] opc_alu_shr;
  assign opc_alu_shr = opc_alu_secondary_i[`OR1K_ALU_OPC_SECONDARY_WIDTH-1:0];
  wire [EXEDW-1:0] shift_result;

  function [EXEDW-1:0] reverse;
  input [EXEDW-1:0] in;
  integer            i;
  begin
    for (i = 0; i < EXEDW; i=i+1) begin
      reverse[(EXEDW-1)-i] = in[i];
    end
  end
  endfunction

  wire op_sll = (opc_alu_shr==`OR1K_ALU_OPC_SECONDARY_SHRT_SLL);
  wire op_srl = (opc_alu_shr==`OR1K_ALU_OPC_SECONDARY_SHRT_SRL);
  wire op_sra = (opc_alu_shr==`OR1K_ALU_OPC_SECONDARY_SHRT_SRA);
  wire op_ror = (opc_alu_shr==`OR1K_ALU_OPC_SECONDARY_SHRT_ROR);

  wire [EXEDW-1:0] shift_right;
  wire [EXEDW-1:0] shift_lsw;
  wire [EXEDW-1:0] shift_msw;

  //
  // Bit-reverse on left shift, perform right shift,
  // bit-reverse result on left shift.
  //
  assign shift_lsw = op_sll ? reverse(a) : a;
  assign shift_msw = op_sra ? {EXEDW{a[EXEDW-1]}} :
                     op_ror ? a : {EXEDW{1'b0}};

  assign shift_right = {shift_msw, shift_lsw} >> b[4:0];
  assign shift_result = op_sll ? reverse(shift_right) : shift_right;



  //-----------------
  // Conditional move
  //-----------------
  wire op_cmov = op_alu_i & (opc_alu_i == `OR1K_ALU_OPC_CMOV);
  wire [EXEDW-1:0] cmov_result;
  assign cmov_result = flag_i ? a : b;



  //-------------------
  // Logical operations
  //-------------------
  // Logic wires
  wire             op_logic;
  reg [EXEDW-1:0]  logic_result;
  // Create a look-up-table for AND/OR/XOR
  reg [3:0] logic_lut;
  always @(*) begin
    case(opc_alu_i)
      `OR1K_ALU_OPC_AND: logic_lut = 4'b1000;
      `OR1K_ALU_OPC_OR:  logic_lut = 4'b1110;
      `OR1K_ALU_OPC_XOR: logic_lut = 4'b0110;
      default:           logic_lut = 4'd0;
    endcase

    if (~op_alu_i)
      logic_lut = 4'd0;

    // Threat mfspr/mtspr as 'OR'
    if (op_mfspr_i | op_mtspr_i)
      logic_lut = 4'b1110;
  end

  // Extract the result, bit-for-bit, from the look-up-table
  integer i;
  always @(*)
    for (i = 0; i < EXEDW; i=i+1) begin
      logic_result[i] = logic_lut[{a[i], b[i]}];
    end

  assign op_logic = |logic_lut;



  //---------------
  // Results muxing
  //---------------
  assign alu_nl_result_o = op_logic        ? logic_result :
                           op_cmov         ? cmov_result :
                           op_movhi_i      ? immediate_i :
                           fpu_arith_valid ? fpu_result :
                           op_shift_i      ? shift_result :
                           op_mul_i        ? mul_result :
                           op_div_i        ? div_result :
                           op_ffl1_i       ? ffl1_result :
                           op_jal_i        ? exec_jal_result_i :  // for GPR[9]
                                             adder_result;


  // Update SR[F] either from integer or float point comparision
  assign exec_flag_set_o   = fpu_op_is_cmp ? (fpu_cmp_flag & fpu_cmp_valid) :
                                             (flag_set & op_setflag_i);
  assign exec_flag_clear_o = fpu_op_is_cmp ? ((~fpu_cmp_flag) & fpu_cmp_valid) :
                                             ((~flag_set) & op_setflag_i);

  // Overflow flag generation
  assign exec_overflow_set_o   = (FEATURE_OVERFLOW != "NONE") &
                                 ((op_add_i & adder_signed_overflow) |
                                  (op_div_signed_i & div_by_zero));
  assign exec_overflow_clear_o = (FEATURE_OVERFLOW != "NONE") &
                                 ((op_add_i & (~adder_signed_overflow)) |
                                  (op_div_signed_i & (~div_by_zero)));

  // Carry flag generation
  assign exec_carry_set_o   = (FEATURE_CARRY_FLAG != "NONE") &
                              ((op_add_i & adder_unsigned_overflow) |
                               (op_div_unsigned_i & div_by_zero));
  assign exec_carry_clear_o = (FEATURE_CARRY_FLAG!="NONE") &
                              ((op_add_i & (~adder_unsigned_overflow)) |
                               (op_div_unsigned_i & (~div_by_zero)));

  // lsu address (not latched)
  assign exec_lsu_adr_o = adder_result;


  //-------------//
  // Stall logic //
  //-------------//

  // ALU wait result
  wire alu_stall =
    (op_div_i & (~div_valid)) |
    (op_mul_i & (~mul_valid)) |
    (fpu_op_is_arith & (~fpu_arith_valid)) |
    (fpu_op_is_cmp & (~fpu_cmp_valid)) |
    ((op_lsu_load_i | op_lsu_store_i) & (~lsu_valid_i) & (~lsu_excepts_i)) |
    (op_msync_i & (~msync_done_i)) |
    (op_mfspr_i & (~ctrl_mfspr_ack_i)) |
    (op_mtspr_i & (~ctrl_mtspr_ack_i));

  // Execute stage can be stalled from ctrl stage and by ALU
  assign exec_valid_o = ~alu_stall;

endmodule // mor1kx_execute_marocchino
