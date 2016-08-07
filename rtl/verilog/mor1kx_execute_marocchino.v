////////////////////////////////////////////////////////////////////////
//                                                                    //
//  mor1kx_execute_marocchino                                         //
//                                                                    //
//  Description: mor1kx execute unit for MAROCCHINO pipeline          //
//               Derived from mor1kx_execute_alu and                  //
//                            mor1kx_execute_ctrl_cappuccino          //
//                                                                    //
////////////////////////////////////////////////////////////////////////
//                                                                    //
//   Copyright (C) 2012 Julius Baxter                                 //
//                      juliusbaxter@gmail.com                        //
//                                                                    //
//   Copyright (C) 2012-2014 Stefan Kristiansson                      //
//                           stefan.kristiansson@saunalahti.fi        //
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


//-------------------//
// 32-bit multiplier //
//-------------------//

module mor1kx_multiplier_marocchino
#(
  parameter OPTION_OPERAND_WIDTH = 32
)
(
  // clocks and resets
  input                                 clk,
  input                                 rst,

  // pipeline control signal in
  input                                 pipeline_flush_i,
  input                                 padv_decode_i,
  input                                 padv_wb_i,
  input                                 grant_wb_to_mul_i,

  // input data
  //   from DECODE
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_rfa_i,
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_rfb_i,
  //   forwarding from WB
  input                                 exe2dec_hazard_a_i,
  input                                 exe2dec_hazard_b_i,
  input      [OPTION_OPERAND_WIDTH-1:0] wb_result_i,

  //  other inputs/outputs
  input                                 dcod_op_mul_i,
  output                                mul_busy_o,
  output                                mul_valid_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] wb_mul_result_o
);

  localparam MULDW  = OPTION_OPERAND_WIDTH; // short name
  localparam MULHDW = (OPTION_OPERAND_WIDTH >> 1);

  // algorithm:
  //   AlBl[dw-1:0] = A[hdw-1:0] * B[hdw-1:0];
  //   AhBl[dw-1:0] = A[dw-1:hdw] * B[hdw-1:0];
  //   BhAl[dw-1:0] = B[dw-1:hdw] * A[hdw-1:0];
  //   Sum[dw-1:0]  = {BhAl[hdw-1:0],{hdw{0}}} +
  //                  {AlBl[hdw-1:0],{hdw{0}}} +
  //                  AlBl;

  // multiplier controls
  //  ## register for input command
  reg    op_mul_r;
  //  ## multiplier stage ready flags
  reg    mul_s1_rdy;
  reg    mul_s2_rdy;
  assign mul_valid_o = mul_s2_rdy; // valid flag is 1-clock ahead of latching for WB
  //  ## stage busy signals
  wire   mul_s2_busy = mul_s2_rdy & ~(padv_wb_i & grant_wb_to_mul_i);
  wire   mul_s1_busy = mul_s1_rdy & mul_s2_busy;
  assign mul_busy_o  = op_mul_r   & mul_s1_busy;
  //  ## stage advance signals
  wire   mul_adv_s2  = mul_s1_rdy & ~mul_s2_busy;
  wire   mul_adv_s1  = op_mul_r   & ~mul_s1_busy;

  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      op_mul_r <= 1'b0;
    else if (pipeline_flush_i)
      op_mul_r <= 1'b0;
    else if (padv_decode_i & dcod_op_mul_i)
      op_mul_r <= 1'b1;
    else if (mul_adv_s1)
      op_mul_r <= 1'b0;
  end // posedge clock

  // operand A latches
  reg  [MULDW-1:0] mul_a_r;        // latched from decode
  reg              mul_fwd_wb_a_r; // use WB result
  wire [MULDW-1:0] mul_a;          // with forwarding from WB
  // operand B latches
  reg  [MULDW-1:0] mul_b_r;        // latched from decode
  reg              mul_fwd_wb_b_r; // use WB result
  wire [MULDW-1:0] mul_b;          // with forwarding from WB
  // new MUL input
  reg              mul_new_insn_r;
  // !!! pay attention that B-operand related hazard is
  // !!! overriden already in OMAN if immediate is used
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      mul_fwd_wb_a_r <= 1'b0;
      mul_fwd_wb_b_r <= 1'b0;
      mul_new_insn_r <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      mul_fwd_wb_a_r <= 1'b0;
      mul_fwd_wb_b_r <= 1'b0;
      mul_new_insn_r <= 1'b0;
    end
    else if (padv_decode_i & dcod_op_mul_i) begin
      mul_fwd_wb_a_r <= exe2dec_hazard_a_i;
      mul_fwd_wb_b_r <= exe2dec_hazard_b_i;
      mul_new_insn_r <= 1'b1;
    end
    else if (mul_new_insn_r) begin // complete forwarding from WB
      mul_fwd_wb_a_r <= 1'b0;
      mul_fwd_wb_b_r <= 1'b0;
      mul_new_insn_r <= 1'b0;
    end
  end // @clock
  // ---
  always @(posedge clk) begin
    if (padv_decode_i & dcod_op_mul_i) begin
      mul_a_r <= dcod_rfa_i;
      mul_b_r <= dcod_rfb_i;
    end
    else if (mul_new_insn_r) begin // complete forwarding from WB
      mul_a_r <= mul_a;
      mul_b_r <= mul_b;
    end
  end // @clock
  // last forward (from WB)
  assign mul_a = mul_fwd_wb_a_r ? wb_result_i : mul_a_r;
  assign mul_b = mul_fwd_wb_b_r ? wb_result_i : mul_b_r;


  // stage #1: register inputs & split them on halfed parts
  reg [MULHDW-1:0] mul_s1_al;
  reg [MULHDW-1:0] mul_s1_bl;
  reg [MULHDW-1:0] mul_s1_ah;
  reg [MULHDW-1:0] mul_s1_bh;
  //  registering
  always @(posedge clk) begin
    if (mul_adv_s1) begin
      mul_s1_al <= mul_a[MULHDW-1:0];
      mul_s1_bl <= mul_b[MULHDW-1:0];
      mul_s1_ah <= mul_a[MULDW-1:MULHDW];
      mul_s1_bh <= mul_b[MULDW-1:MULHDW];
    end
  end // posedge clock
  //  ready flag
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      mul_s1_rdy <= 1'b0;
    else if (pipeline_flush_i)
      mul_s1_rdy <= 1'b0;
    else if (mul_adv_s1)
      mul_s1_rdy <= 1'b1;
    else if (mul_adv_s2)
      mul_s1_rdy <= 1'b0;
  end // posedge clock

  // stage #2: partial products
  reg [MULDW-1:0] mul_s2_albl;
  reg [MULDW-1:0] mul_s2_ahbl;
  reg [MULDW-1:0] mul_s2_bhal;
  //  registering
  always @(posedge clk) begin
    if (mul_adv_s2) begin
      mul_s2_albl <= mul_s1_al * mul_s1_bl;
      mul_s2_ahbl <= mul_s1_ah * mul_s1_bl;
      mul_s2_bhal <= mul_s1_bh * mul_s1_al;
    end
  end // posedge clock
  //  ready flag
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      mul_s2_rdy <= 1'b0;
    else if (pipeline_flush_i)
      mul_s2_rdy <= 1'b0;
    else if (mul_adv_s2)
      mul_s2_rdy <= 1'b1;
    else if (padv_wb_i & grant_wb_to_mul_i)
      mul_s2_rdy <= 1'b0;
  end // posedge clock

  // stage #3: result
  wire [MULDW-1:0] mul_s3t_sum;
  assign mul_s3t_sum = {mul_s2_bhal[MULHDW-1:0],{MULHDW{1'b0}}} +
                       {mul_s2_ahbl[MULHDW-1:0],{MULHDW{1'b0}}} +
                        mul_s2_albl;
  //  registering
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_mul_result_o <= {MULDW{1'b0}};
    else if (padv_wb_i)
      wb_mul_result_o <= {MULDW{grant_wb_to_mul_i}} & mul_s3t_sum;
  end // posedge clock

endmodule // mor1kx_multiplier_marocchino



//----------------//
// 32-bit divider //
//----------------//

module mor1kx_divider_marocchino
#(
  parameter OPTION_OPERAND_WIDTH = 32
)
(
  // clocks and resets
  input                                 clk,
  input                                 rst,

  // pipeline control signal in
  input                                 pipeline_flush_i,
  input                                 padv_decode_i,
  input                                 padv_wb_i,
  input                                 grant_wb_to_div_i,

  // input data
  //   from DECODE
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_rfa_i,
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_rfb_i,
  //   forwarding from WB
  input                                 exe2dec_hazard_a_i,
  input                                 exe2dec_hazard_b_i,
  input      [OPTION_OPERAND_WIDTH-1:0] wb_result_i,

  // division command
  input                                 dcod_op_div_i,
  input                                 dcod_op_div_signed_i,
  input                                 dcod_op_div_unsigned_i,

  // division engine state
  output                                div_busy_o,
  output reg                            div_valid_o,

  // write back
  //  # update carry flag by division
  output reg                            wb_div_carry_set_o,
  output reg                            wb_div_carry_clear_o,
  //  # update overflow flag by division
  output reg                            wb_div_overflow_set_o,
  output reg                            wb_div_overflow_clear_o,
  //  # generate overflow exception by division
  input                                 except_overflow_enable_i,
  output reg                            wb_except_overflow_div_o,
  //  # division result
  output reg [OPTION_OPERAND_WIDTH-1:0] wb_div_result_o
);

  localparam DIVDW  = OPTION_OPERAND_WIDTH; // short name

  // divider controls
  //  ## register for input command
  reg  op_div_r;
  reg  op_div_signed_r;
  reg  op_div_unsigned_r;
  //  ## iterations counter
  reg [5:0] div_count;
  reg       div_proc_r;
  //  ## start division
  wire take_op_div = op_div_r & (div_valid_o ? (padv_wb_i & grant_wb_to_div_i) : ~div_proc_r);
  //  ## outbut busy flag
  assign div_busy_o = op_div_r & ~(div_valid_o ? (padv_wb_i & grant_wb_to_div_i) : ~div_proc_r);

  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      op_div_r          <= 1'b0;
      op_div_signed_r   <= 1'b0;
      op_div_unsigned_r <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      op_div_r          <= 1'b0;
      op_div_signed_r   <= 1'b0;
      op_div_unsigned_r <= 1'b0;
    end
    else if (padv_decode_i & dcod_op_div_i) begin
      op_div_r          <= 1'b1;
      op_div_signed_r   <= dcod_op_div_signed_i;
      op_div_unsigned_r <= dcod_op_div_unsigned_i;
    end
    else if (take_op_div) begin
      op_div_r          <= 1'b0;
      op_div_signed_r   <= 1'b0;
      op_div_unsigned_r <= 1'b0;
    end
  end // posedge clock

  // operand A latches
  reg [DIVDW-1:0]  div_a_r;        // latched from decode
  reg              div_fwd_wb_a_r; // use WB result
  wire [DIVDW-1:0] div_a;          // with forwarding from WB
  // operand B latches
  reg [DIVDW-1:0]  div_b_r;        // latched from decode
  reg              div_fwd_wb_b_r; // use WB result
  wire [DIVDW-1:0] div_b;          // with forwarding from WB
  // new DIV input
  reg              div_new_insn_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      div_fwd_wb_a_r <= 1'b0;
      div_fwd_wb_b_r <= 1'b0;
      div_new_insn_r <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      div_fwd_wb_a_r <= 1'b0;
      div_fwd_wb_b_r <= 1'b0;
      div_new_insn_r <= 1'b0;
    end
    else if (padv_decode_i & dcod_op_div_i) begin
      div_fwd_wb_a_r <= exe2dec_hazard_a_i;
      div_fwd_wb_b_r <= exe2dec_hazard_b_i;
      div_new_insn_r <= 1'b1;
    end
    else if (div_new_insn_r) begin // complete forwarding from WB
      div_fwd_wb_a_r <= 1'b0;
      div_fwd_wb_b_r <= 1'b0;
      div_new_insn_r <= 1'b0;
    end
  end // @clock
  // ---
  always @(posedge clk) begin
    if (padv_decode_i & dcod_op_div_i) begin
      div_a_r <= dcod_rfa_i;
      div_b_r <= dcod_rfb_i; // opposite to multiply, no IMM as operand
    end
    else if (div_new_insn_r) begin // complete forwarding from WB
      div_a_r <= div_a;
      div_b_r <= div_b;
    end
  end // @clock
  // last forward (from WB)
  assign div_a = div_fwd_wb_a_r ? wb_result_i : div_a_r;
  assign div_b = div_fwd_wb_b_r ? wb_result_i : div_b_r;

  // division controller
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      div_valid_o <= 1'b0;
      div_proc_r  <= 1'b0;
      div_count   <= 6'd0;
    end
    if (pipeline_flush_i) begin
      div_valid_o <= 1'b0;
      div_proc_r  <= 1'b0;
      div_count   <= 6'd0;
    end
    else if (take_op_div) begin
      div_valid_o <= 1'b0;
      div_proc_r  <= 1'b1;
      div_count   <= DIVDW;
    end
    else if (div_valid_o & padv_wb_i & grant_wb_to_div_i) begin
      div_valid_o <= 1'b0;
      div_proc_r  <= div_busy_o;
      div_count   <= div_count;
    end
    else if (div_proc_r) begin
      if (div_count == 6'd1) begin
        div_valid_o <= 1'b1;
        div_proc_r  <= 1'b0;
      end
      div_count <= div_count - 6'd1;
    end
  end // @clock

  // regs of divider
  reg [DIVDW-1:0] div_n;
  reg [DIVDW-1:0] div_d;
  reg [DIVDW-1:0] div_r;
  reg             div_signed, div_unsigned;
  reg             div_neg;
  reg             dbz_r;

  // signums of input operands
  wire op_div_sign_a = div_a[DIVDW-1] & op_div_signed_r;
  wire op_div_sign_b = div_b[DIVDW-1] & op_div_signed_r;

  // partial reminder
  wire [DIVDW:0] div_sub = {div_r[DIVDW-2:0],div_n[DIVDW-1]} - div_d;

  always @(posedge clk) begin
    if (take_op_div) begin
      // Convert negative operands in the case of signed division.
      // If only one of the operands is negative, the result is
      // converted back to negative later on
      div_n   <= (div_a ^ {DIVDW{op_div_sign_a}}) + {{(DIVDW-1){1'b0}},op_div_sign_a};
      div_d   <= (div_b ^ {DIVDW{op_div_sign_b}}) + {{(DIVDW-1){1'b0}},op_div_sign_b};
      div_r   <= {DIVDW{1'b0}};
      div_neg <= (op_div_sign_a ^ op_div_sign_b);
      dbz_r   <= ~(|div_b);
      div_signed   <= op_div_signed_r;
      div_unsigned <= op_div_unsigned_r;
    end
    else if (~div_valid_o) begin
      if (~div_sub[DIVDW]) begin // div_sub >= 0
        div_r <= div_sub[DIVDW-1:0];
        div_n <= {div_n[DIVDW-2:0], 1'b1};
      end
      else begin                 // div_sub < 0
        div_r <= {div_r[DIVDW-2:0],div_n[DIVDW-1]};
        div_n <= {div_n[DIVDW-2:0], 1'b0};
      end
    end // ~done
  end // @clock

  wire [DIVDW-1:0] div_result = (div_n ^ {DIVDW{div_neg}}) + {{(DIVDW-1){1'b0}},div_neg};

  /**** DIV Write Back result ****/
  
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_div_result_o <= {DIVDW{1'b0}};
    else if (padv_wb_i)
      wb_div_result_o <= {DIVDW{grant_wb_to_div_i}} & div_result;
  end // posedge clock

  /****  DIV Write Back flags ****/

  //  # update carry flag by division
  wire exec_div_carry_set      = grant_wb_to_div_i & div_unsigned &   dbz_r;
  wire exec_div_carry_clear    = grant_wb_to_div_i & div_unsigned & (~dbz_r);

  //  # update overflow flag by division
  wire exec_div_overflow_set   = grant_wb_to_div_i & div_signed &   dbz_r;
  wire exec_div_overflow_clear = grant_wb_to_div_i & div_signed & (~dbz_r);

  //  # generate overflow exception by division
  wire exec_except_overflow_div = except_overflow_enable_i & exec_div_overflow_set;

  // WB-latchers
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      //  # update carry flag by division
      wb_div_carry_set_o        <= 1'b0;
      wb_div_carry_clear_o      <= 1'b0;
      //  # update overflow flag by division
      wb_div_overflow_set_o     <= 1'b0;
      wb_div_overflow_clear_o   <= 1'b0;
      //  # generate overflow exception by division
      wb_except_overflow_div_o  <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      //  # update carry flag by division
      wb_div_carry_set_o        <= 1'b0;
      wb_div_carry_clear_o      <= 1'b0;
      //  # update overflow flag by division
      wb_div_overflow_set_o     <= 1'b0;
      wb_div_overflow_clear_o   <= 1'b0;
      //  # generate overflow exception by division
      wb_except_overflow_div_o  <= 1'b0;
    end
    else if (padv_wb_i) begin
      //  # update carry flag by division
      wb_div_carry_set_o        <= exec_div_carry_set;
      wb_div_carry_clear_o      <= exec_div_carry_clear;
      //  # update overflow flag by division
      wb_div_overflow_set_o     <= exec_div_overflow_set;
      wb_div_overflow_clear_o   <= exec_div_overflow_clear;
      //  # generate overflow exception by division
      wb_except_overflow_div_o  <= exec_except_overflow_div;
    end
  end // @clock
  
endmodule // mor1kx_divider_marocchino



//-----------------------------------------------//
// 1-clock operations including FP-32 comparison //
//-----------------------------------------------//

module mor1kx_exec_1clk_marocchino
#(
  parameter OPTION_OPERAND_WIDTH = 32,
  parameter OPTION_RF_ADDR_WIDTH =  5,
  parameter FEATURE_EXT          = "NONE",
  parameter FEATURE_FPU          = "NONE" // ENABLED|NONE
)
(
  // clocks and resets
  input                                 clk,
  input                                 rst,

  // pipeline control signal in
  input                                 pipeline_flush_i,
  input                                 padv_decode_i,
  input                                 padv_wb_i,
  input                                 grant_wb_to_1clk_i,

  // input data
  //   from DECODE
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_rfa_i,
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_rfb_i,
  //   forwarding from WB
  input                                 exe2dec_hazard_a_i,
  input                                 exe2dec_hazard_b_i,
  input      [OPTION_OPERAND_WIDTH-1:0] wb_result_i,

  // 1-clock instruction auxiliaries
  input                                 dcod_op_1clk_i,
  output                                op_1clk_busy_o,
  input       [`OR1K_ALU_OPC_WIDTH-1:0] dcod_opc_alu_secondary_i,
  input                                 carry_i, // feedback from ctrl
  input                                 flag_i, // feedback from ctrl (for cmov)

  // adder's inputs
  input                                 dcod_op_add_i,
  input                                 dcod_adder_do_sub_i,
  input                                 dcod_adder_do_carry_i,
  // shift, ffl1, movhi, cmov
  input                                 dcod_op_shift_i,
  input                                 dcod_op_ffl1_i,
  input                                 dcod_op_movhi_i,
  input                                 dcod_op_cmov_i,
  // logic
  input       [`OR1K_ALU_OPC_WIDTH-1:0] dcod_opc_logic_i,
  // jump & link
  input                                 dcod_op_jal_i,
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_jal_result_i,
  // WB-latched 1-clock arithmetic result
  output reg [OPTION_OPERAND_WIDTH-1:0] wb_alu_1clk_result_o,
  //  # update carry flag by 1clk-operation
  output reg                            wb_1clk_carry_set_o,
  output reg                            wb_1clk_carry_clear_o,
  //  # update overflow flag by 1clk-operation
  output reg                            wb_1clk_overflow_set_o,
  output reg                            wb_1clk_overflow_clear_o,
  //  # generate overflow exception by 1clk-operation
  input                                 except_overflow_enable_i,
  output reg                            wb_except_overflow_1clk_o,

  // integer comparison flag
  input                                 dcod_op_setflag_i,
  // WB: integer comparison result
  output reg                            wb_int_flag_set_o,
  output reg                            wb_int_flag_clear_o,

  // FP32 comparison flag
  input         [`OR1K_FPUOP_WIDTH-1:0] dcod_op_fp32_cmp_i,
  input                                 except_fpu_enable_i,
  input                                 ctrl_fpu_mask_flags_inv_i,
  input                                 ctrl_fpu_mask_flags_inf_i,
  // WB: FP32 comparison results
  output                                wb_fp32_flag_set_o,
  output                                wb_fp32_flag_clear_o,
  output                                wb_fp32_cmp_inv_o,
  output                                wb_fp32_cmp_inf_o,
  output                                wb_fp32_cmp_wb_fpcsr_o,
  output                                wb_except_fp32_cmp_o,

  // Forwarding comparision flag result for conditional branch take/not
  output                                exec_op_1clk_cmp_o, // integer or fp32
  output                                exec_flag_set_o     // integer or fp32 comparison result
);

  localparam  EXEDW = OPTION_OPERAND_WIDTH; // short name


  // single clock operations controls
  //  # opcode for alu
  reg [`OR1K_ALU_OPC_WIDTH-1:0] opc_alu_secondary_r;
  //  # adder's inputs
  reg                           op_add_r;
  reg                           adder_do_sub_r;
  reg                           adder_do_carry_r;
  //  # shift, ffl1, movhi, cmov
  reg                           op_shift_r;
  reg                           op_ffl1_r;
  reg                           op_movhi_r;
  reg                           op_cmov_r;
  //  # logic
  reg                           op_logic_r;
  reg [`OR1K_ALU_OPC_WIDTH-1:0] opc_logic_r;
  //  # jump & link
  reg                           op_jal_r;
  reg               [EXEDW-1:0] jal_result_r;
  //  # flag related inputs
  reg                           op_setflag_r;
  reg   [`OR1K_FPUOP_WIDTH-1:0] op_fp32_cmp_r;

  // flag that 1-clock instruction is executed
  reg op_1clk_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      op_1clk_r <= 1'b0;
    else if (pipeline_flush_i)
      op_1clk_r <= 1'b0;
    else if (padv_decode_i & dcod_op_1clk_i)
      op_1clk_r <= 1'b1;
    else if (padv_wb_i & grant_wb_to_1clk_i)
      op_1clk_r <= 1'b0;
  end // posedge clock

  // busy signal for 1-clock units
  assign op_1clk_busy_o = op_1clk_r & ~(padv_wb_i & grant_wb_to_1clk_i);

  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      // opcode for alu
      opc_alu_secondary_r <= {`OR1K_ALU_OPC_WIDTH{1'b0}};
      // adder's inputs
      op_add_r            <= 1'b0;
      adder_do_sub_r      <= 1'b0;
      adder_do_carry_r    <= 1'b0;
      // shift, ffl1, movhi, cmov
      op_shift_r          <= 1'b0;
      op_ffl1_r           <= 1'b0;
      op_movhi_r          <= 1'b0;
      op_cmov_r           <= 1'b0;
      // logic
      op_logic_r          <= 1'b0;
      opc_logic_r         <= {`OR1K_ALU_OPC_WIDTH{1'b0}};
      // jump & link
      op_jal_r            <= 1'b0;
      jal_result_r        <= {EXEDW{1'b0}};
      // flag related inputs
      op_setflag_r        <= 1'b0;
      op_fp32_cmp_r       <= {`OR1K_FPUOP_WIDTH{1'b0}};
    end
    else if (pipeline_flush_i) begin
      // opcode for alu
      opc_alu_secondary_r <= {`OR1K_ALU_OPC_WIDTH{1'b0}};
      // adder's inputs
      op_add_r            <= 1'b0;
      adder_do_sub_r      <= 1'b0;
      adder_do_carry_r    <= 1'b0;
      // shift, ffl1, movhi, cmov
      op_shift_r          <= 1'b0;
      op_ffl1_r           <= 1'b0;
      op_movhi_r          <= 1'b0;
      op_cmov_r           <= 1'b0;
      // logic
      op_logic_r          <= 1'b0;
      opc_logic_r         <= {`OR1K_ALU_OPC_WIDTH{1'b0}};
      // jump & link
      op_jal_r            <= 1'b0;
      jal_result_r        <= {EXEDW{1'b0}};
      // flag related inputs
      op_setflag_r        <= 1'b0;
      op_fp32_cmp_r       <= {`OR1K_FPUOP_WIDTH{1'b0}};
    end
    else if (padv_decode_i & dcod_op_1clk_i) begin
      // opcode for alu
      opc_alu_secondary_r <= dcod_opc_alu_secondary_i;
      // adder's inputs
      op_add_r            <= dcod_op_add_i;
      adder_do_sub_r      <= dcod_adder_do_sub_i;
      adder_do_carry_r    <= dcod_adder_do_carry_i;
      // shift, ffl1, movhi, cmov
      op_shift_r          <= dcod_op_shift_i;
      op_ffl1_r           <= dcod_op_ffl1_i;
      op_movhi_r          <= dcod_op_movhi_i;
      op_cmov_r           <= dcod_op_cmov_i;
      // logic
      op_logic_r          <= (|dcod_opc_logic_i);
      opc_logic_r         <= dcod_opc_logic_i;
      // jump & link
      op_jal_r            <= dcod_op_jal_i;
      jal_result_r        <= dcod_jal_result_i;
      // flag related inputs
      op_setflag_r        <= dcod_op_setflag_i;
      op_fp32_cmp_r       <= dcod_op_fp32_cmp_i;
    end
  end // posedge clock

  // operand A latches
  reg  [EXEDW-1:0] alu_1clk_a_r;        // latched from decode
  reg              alu_1clk_fwd_wb_a_r; // use WB result
  wire [EXEDW-1:0] alu_1clk_a;          // with forwarding from WB
  // operand B latches
  reg  [EXEDW-1:0] alu_1clk_b_r;        // latched from decode
  reg              alu_1clk_fwd_wb_b_r; // use WB result
  wire [EXEDW-1:0] alu_1clk_b;          // with forwarding from WB
  // new MUL input
  reg              alu_1clk_new_insn_r;
  // !!! pay attention that B-operand related hazard is
  // !!! overriden already in OMAN if immediate is used
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      alu_1clk_fwd_wb_a_r <= 1'b0;
      alu_1clk_fwd_wb_b_r <= 1'b0;
      alu_1clk_new_insn_r <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      alu_1clk_fwd_wb_a_r <= 1'b0;
      alu_1clk_fwd_wb_b_r <= 1'b0;
      alu_1clk_new_insn_r <= 1'b0;
    end
    else if (padv_decode_i & dcod_op_1clk_i) begin
      alu_1clk_fwd_wb_a_r <= exe2dec_hazard_a_i;
      alu_1clk_fwd_wb_b_r <= exe2dec_hazard_b_i;
      alu_1clk_new_insn_r <= 1'b1;
    end
    else if (alu_1clk_new_insn_r) begin // complete forwarding from WB
      alu_1clk_fwd_wb_a_r <= 1'b0;
      alu_1clk_fwd_wb_b_r <= 1'b0;
      alu_1clk_new_insn_r <= 1'b0;
    end
  end // @clock
  // ---
  always @(posedge clk) begin
    if (padv_decode_i & dcod_op_1clk_i) begin
      alu_1clk_a_r <= dcod_rfa_i;
      alu_1clk_b_r <= dcod_rfb_i;
    end
    else if (alu_1clk_new_insn_r) begin // complete forwarding from WB
      alu_1clk_a_r <= alu_1clk_a;
      alu_1clk_b_r <= alu_1clk_b;
    end
  end // @clock
  // last forward (from WB)
  assign alu_1clk_a = alu_1clk_fwd_wb_a_r ? wb_result_i : alu_1clk_a_r;
  assign alu_1clk_b = alu_1clk_fwd_wb_b_r ? wb_result_i : alu_1clk_b_r;


  //------------------//
  // Adder/subtractor //
  //------------------//
  // outputs
  wire             adder_carryout;
  wire [EXEDW-1:0] adder_result;
  // inputs
  wire [EXEDW-1:0] b_mux = adder_do_sub_r ? (~alu_1clk_b) : alu_1clk_b;
  wire carry_in = adder_do_sub_r | (adder_do_carry_r & carry_i);
  // Adder
  assign {adder_carryout, adder_result} =
           alu_1clk_a + b_mux + {{(EXEDW-1){1'b0}},carry_in};
  // result sign
  wire adder_result_sign = adder_result[EXEDW-1];
  // signed overflow detection
  // Input signs are same and result sign is different to input signs
  wire adder_s_ovf =
         (alu_1clk_a[EXEDW-1] == b_mux[EXEDW-1]) &
         (alu_1clk_a[EXEDW-1] ^ adder_result[EXEDW-1]);
  // unsigned overflow detection
  wire adder_u_ovf = adder_carryout;


  //------//
  // FFL1 //
  //------//
  wire [EXEDW-1:0] ffl1_result;
  assign ffl1_result = (opc_alu_secondary_r[2]) ?
           (alu_1clk_a[31] ? 32 : alu_1clk_a[30] ? 31 : alu_1clk_a[29] ? 30 :
            alu_1clk_a[28] ? 29 : alu_1clk_a[27] ? 28 : alu_1clk_a[26] ? 27 :
            alu_1clk_a[25] ? 26 : alu_1clk_a[24] ? 25 : alu_1clk_a[23] ? 24 :
            alu_1clk_a[22] ? 23 : alu_1clk_a[21] ? 22 : alu_1clk_a[20] ? 21 :
            alu_1clk_a[19] ? 20 : alu_1clk_a[18] ? 19 : alu_1clk_a[17] ? 18 :
            alu_1clk_a[16] ? 17 : alu_1clk_a[15] ? 16 : alu_1clk_a[14] ? 15 :
            alu_1clk_a[13] ? 14 : alu_1clk_a[12] ? 13 : alu_1clk_a[11] ? 12 :
            alu_1clk_a[10] ? 11 : alu_1clk_a[9] ? 10 : alu_1clk_a[8] ? 9 :
            alu_1clk_a[7] ? 8 : alu_1clk_a[6] ? 7 : alu_1clk_a[5] ? 6 : alu_1clk_a[4] ? 5 :
            alu_1clk_a[3] ? 4 : alu_1clk_a[2] ? 3 : alu_1clk_a[1] ? 2 : alu_1clk_a[0] ? 1 : 0 ) :
           (alu_1clk_a[0] ? 1 : alu_1clk_a[1] ? 2 : alu_1clk_a[2] ? 3 : alu_1clk_a[3] ? 4 :
            alu_1clk_a[4] ? 5 : alu_1clk_a[5] ? 6 : alu_1clk_a[6] ? 7 : alu_1clk_a[7] ? 8 :
            alu_1clk_a[8] ? 9 : alu_1clk_a[9] ? 10 : alu_1clk_a[10] ? 11 : alu_1clk_a[11] ? 12 :
            alu_1clk_a[12] ? 13 : alu_1clk_a[13] ? 14 : alu_1clk_a[14] ? 15 :
            alu_1clk_a[15] ? 16 : alu_1clk_a[16] ? 17 : alu_1clk_a[17] ? 18 :
            alu_1clk_a[18] ? 19 : alu_1clk_a[19] ? 20 : alu_1clk_a[20] ? 21 :
            alu_1clk_a[21] ? 22 : alu_1clk_a[22] ? 23 : alu_1clk_a[23] ? 24 :
            alu_1clk_a[24] ? 25 : alu_1clk_a[25] ? 26 : alu_1clk_a[26] ? 27 :
            alu_1clk_a[27] ? 28 : alu_1clk_a[28] ? 29 : alu_1clk_a[29] ? 30 :
            alu_1clk_a[30] ? 31 : alu_1clk_a[31] ? 32 : 0);


  //----------------//
  // Barrel shifter //
  //----------------//

  // Bit-reverse on left shift, perform right shift,
  // bit-reverse result on left shift.

  function [EXEDW-1:0] reverse;
  input [EXEDW-1:0] in;
  integer            i;
  begin
    for (i = 0; i < EXEDW; i=i+1) begin
      reverse[(EXEDW-1)-i] = in[i];
    end
  end
  endfunction

  wire op_sll = (opc_alu_secondary_r == `OR1K_ALU_OPC_SECONDARY_SHRT_SLL);
  wire op_srl = (opc_alu_secondary_r == `OR1K_ALU_OPC_SECONDARY_SHRT_SRL);
  wire op_sra = (opc_alu_secondary_r == `OR1K_ALU_OPC_SECONDARY_SHRT_SRA);
  wire op_ror = (opc_alu_secondary_r == `OR1K_ALU_OPC_SECONDARY_SHRT_ROR);

  wire [EXEDW-1:0] shift_right;
  wire [EXEDW-1:0] shift_lsw;
  wire [EXEDW-1:0] shift_msw;

  wire [EXEDW-1:0] shift_result;

  assign shift_lsw = op_sll ? reverse(alu_1clk_a) : alu_1clk_a;
  assign shift_msw = op_sra ? {EXEDW{alu_1clk_a[EXEDW-1]}} :
                     op_ror ? alu_1clk_a : {EXEDW{1'b0}};

  assign shift_right = {shift_msw, shift_lsw} >> alu_1clk_b[4:0];
  assign shift_result = op_sll ? reverse(shift_right) : shift_right;


  //------------------//
  // Conditional move //
  //------------------//
  wire [EXEDW-1:0] cmov_result;
  assign cmov_result = flag_i ? alu_1clk_a : alu_1clk_b;


  //--------------------//
  // Logical operations //
  //--------------------//
  // Logic wires
  reg [EXEDW-1:0]  logic_result;
  // Create a look-up-table for AND/OR/XOR
  reg [3:0] logic_lut;
  always @(*) begin
    case(opc_logic_r)
      `OR1K_ALU_OPC_AND: logic_lut = 4'b1000;
      `OR1K_ALU_OPC_OR:  logic_lut = 4'b1110;
      `OR1K_ALU_OPC_XOR: logic_lut = 4'b0110;
      default:           logic_lut = 4'd0;
    endcase
  end
  // Extract the result, bit-for-bit, from the look-up-table
  integer i;
  always @(*) begin
    for (i = 0; i < EXEDW; i=i+1) begin
      logic_result[i] = logic_lut[{alu_1clk_a[i], alu_1clk_b[i]}];
    end
  end


  //------------------------------------------------------------------//
  // Muxing and registering 1-clk results and integer comparison flag //
  //------------------------------------------------------------------//
  wire [EXEDW-1:0] alu_1clk_result_mux = ({EXEDW{op_shift_r}} & shift_result ) |
                                         ({EXEDW{op_ffl1_r}}  & ffl1_result  ) |
                                         ({EXEDW{op_add_r}}   & adder_result ) |
                                         ({EXEDW{op_logic_r}} & logic_result ) |
                                         ({EXEDW{op_cmov_r}}  & cmov_result  ) |
                                         ({EXEDW{op_movhi_r}} & alu_1clk_b   ) |
                                         ({EXEDW{op_jal_r}}   & jal_result_r ); // for GPR[9]

  //  registering output for 1-clock operations
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_alu_1clk_result_o <= {EXEDW{1'b0}};
    else if (padv_wb_i)
      wb_alu_1clk_result_o <= {EXEDW{grant_wb_to_1clk_i}} & alu_1clk_result_mux;
  end // posedge clock

  /****  1CLK Write Back flags ****/

  //  # update carry flag by 1clk-operation
  wire exec_1clk_carry_set      = grant_wb_to_1clk_i & op_add_r &   adder_u_ovf;
  wire exec_1clk_carry_clear    = grant_wb_to_1clk_i & op_add_r & (~adder_u_ovf);

  //  # update overflow flag by 1clk-operation
  wire exec_1clk_overflow_set   = grant_wb_to_1clk_i & op_add_r &   adder_s_ovf;
  wire exec_1clk_overflow_clear = grant_wb_to_1clk_i & op_add_r & (~adder_s_ovf);

  //  # generate overflow exception by 1clk-operation
  wire exec_except_overflow_1clk = except_overflow_enable_i & exec_1clk_overflow_set;

  // WB-latchers
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      //  # update carry flag by 1clk-operation
      wb_1clk_carry_set_o        <= 1'b0;
      wb_1clk_carry_clear_o      <= 1'b0;
      //  # update overflow flag by 1clk-operation
      wb_1clk_overflow_set_o     <= 1'b0;
      wb_1clk_overflow_clear_o   <= 1'b0;
      //  # generate overflow exception by 1clk-operation
      wb_except_overflow_1clk_o  <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      //  # update carry flag by 1clk-operation
      wb_1clk_carry_set_o        <= 1'b0;
      wb_1clk_carry_clear_o      <= 1'b0;
      //  # update overflow flag by 1clk-operation
      wb_1clk_overflow_set_o     <= 1'b0;
      wb_1clk_overflow_clear_o   <= 1'b0;
      //  # generate overflow exception by 1clk-operation
      wb_except_overflow_1clk_o  <= 1'b0;
    end
    else if (padv_wb_i) begin
      //  # update carry flag by 1clk-operation
      wb_1clk_carry_set_o        <= exec_1clk_carry_set;
      wb_1clk_carry_clear_o      <= exec_1clk_carry_clear;
      //  # update overflow flag by 1clk-operation
      wb_1clk_overflow_set_o     <= exec_1clk_overflow_set;
      wb_1clk_overflow_clear_o   <= exec_1clk_overflow_clear;
      //  # generate overflow exception by 1clk-operation
      wb_except_overflow_1clk_o  <= exec_except_overflow_1clk;
    end
  end // @clock


  //--------------------------//
  // Integer comparison logic //
  //--------------------------//
  wire a_eq_b  = (alu_1clk_a == alu_1clk_b); // Equal compare
  wire a_lts_b = (adder_result_sign ^ adder_s_ovf); // Signed compare (sign != ovf)
  wire a_ltu_b = ~adder_carryout; // Unsigned compare
  // comb.
  reg flag_set;
  always @* begin
    case(opc_alu_secondary_r)
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
  end
  // latched integer comparison result for WB
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      wb_int_flag_set_o   <= 1'b0;
      wb_int_flag_clear_o <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      wb_int_flag_set_o   <= 1'b0;
      wb_int_flag_clear_o <= 1'b0;
    end
    else if (padv_wb_i) begin
      wb_int_flag_set_o   <= op_setflag_r & grant_wb_to_1clk_i &   flag_set;
      wb_int_flag_clear_o <= op_setflag_r & grant_wb_to_1clk_i & (~flag_set);
    end // wb advance
  end // @clock


  //------------------------//
  // FP-32 comparison logic //
  //------------------------//
  wire fp32_flag_set; // for forwarding to branch prediction
  // ---
  generate
  /* verilator lint_off WIDTH */
  if (FEATURE_FPU != "NONE") begin :  alu_fp32_cmp_ena
  /* verilator lint_on WIDTH */
    pfpu32_fcmp_marocchino u_f32_cmp
    (
      // clocks, resets and other controls
      .clk                    (clk),
      .rst                    (rst),
      .flush_i                (pipeline_flush_i),   // fp32-cmp flush pipe
      .padv_wb_i              (padv_wb_i),          // fp32-cmp. advance output latches
      .grant_wb_to_1clk_i     (grant_wb_to_1clk_i), // fp32-cmp
      // command
      .fpu_op_is_comp_i       (op_fp32_cmp_r[`OR1K_FPUOP_WIDTH-1]), // fp32-cmp
      .cmp_type_i             ({1'b0,op_fp32_cmp_r[`OR1K_FPUOP_WIDTH-2:0]}), // fp32-cmp
      // Operands
      .rfa_i                  (alu_1clk_a), // fp32-cmp
      .rfb_i                  (alu_1clk_b), // fp32-cmp
      // Modes
      .except_fpu_enable_i        (except_fpu_enable_i), // fp32-cmp
      .ctrl_fpu_mask_flags_inv_i  (ctrl_fpu_mask_flags_inv_i), // fp32-cmp
      .ctrl_fpu_mask_flags_inf_i  (ctrl_fpu_mask_flags_inf_i), // fp32-cmp
      // Outputs
      //  # not WB-latched for flag forwarding
      .fp32_flag_set_o        (fp32_flag_set),
      //  # WB-latched
      .wb_fp32_flag_set_o     (wb_fp32_flag_set_o),   // fp32-cmp  result
      .wb_fp32_flag_clear_o   (wb_fp32_flag_clear_o), // fp32-cmp  result
      .wb_fp32_cmp_inv_o      (wb_fp32_cmp_inv_o), // fp32-cmp flag 'invalid'
      .wb_fp32_cmp_inf_o      (wb_fp32_cmp_inf_o), // fp32-cmp flag 'infinity'
      .wb_fp32_cmp_wb_fpcsr_o (wb_fp32_cmp_wb_fpcsr_o), // fp32-cmp update FPCSR
      .wb_except_fp32_cmp_o   (wb_except_fp32_cmp_o) // fp32-cmp exception
    );
  end
  else begin :  alu_fp32_cmp_none
    assign fp32_flag_set          = 1'b0;
    assign wb_fp32_flag_set_o     = 1'b0;
    assign wb_fp32_flag_clear_o   = 1'b0;
    assign wb_fp32_cmp_inv_o      = 1'b0;
    assign wb_fp32_cmp_inf_o      = 1'b0;
    assign wb_fp32_cmp_wb_fpcsr_o = 1'b0;
    assign wb_except_fp32_cmp_o   = 1'b0;
  end // fpu_ena/fpu_none
  endgenerate // FP-32 comparison part related


  //--------------------------------------------------//
  // Forwarding comparision flag to branch prediction //
  //--------------------------------------------------//
  assign exec_op_1clk_cmp_o = op_setflag_r | op_fp32_cmp_r[`OR1K_FPUOP_WIDTH-1];
  assign exec_flag_set_o    = (op_setflag_r & flag_set) | (op_fp32_cmp_r[`OR1K_FPUOP_WIDTH-1] & fp32_flag_set);

endmodule // mor1kx_exec_1clk_marocchino
