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
  parameter FEATURE_EXT          = "NONE",
  parameter FEATURE_FPU          = "NONE" // ENABLED|NONE
)
(
  // clocks and resets
  input                                 clk,
  input                                 rst,

  // pipeline control signal in
  input                                 padv_decode_i,
  input                                 padv_wb_i,
  input                                 pipeline_flush_i,// flush pipelined fpu

  // input data
  input      [OPTION_OPERAND_WIDTH-1:0] rfa_i,
  input      [OPTION_OPERAND_WIDTH-1:0] rfb_i,
  input      [OPTION_OPERAND_WIDTH-1:0] immediate_i,
  input                                 immediate_sel_i,

  // various instruction related flags & data
  input                                 exec_bubble_i,      // empty istruction
  input      [OPTION_RF_ADDR_WIDTH-1:0] exec_rfd_adr_i,     // desination address
  input                                 exec_rf_wb_i,       // WB-request
  input      [OPTION_OPERAND_WIDTH-1:0] pc_exec_i,          // insn. address
  input                                 exec_delay_slot_i,  // delay slot

  // 1-clock instruction related inputs
  input                                 exec_insn_1clk_i,
  //  # opcode for alu
  input       [`OR1K_ALU_OPC_WIDTH-1:0] opc_alu_i,
  input       [`OR1K_ALU_OPC_WIDTH-1:0] opc_alu_secondary_i,
  //  # adder's inputs
  input                                 op_add_i,
  input                                 adder_do_sub_i,
  input                                 adder_do_carry_i,
  input                                 carry_i,
  //  # shift, ffl1, movhi, cmov
  input                                 op_shift_i,
  input                                 op_ffl1_i,
  input                                 op_movhi_i,
  input                                 op_cmov_i,
  //  # jump & link
  input                                 op_jal_i,
  input      [OPTION_OPERAND_WIDTH-1:0] exec_jal_result_i,
  //  # flag related inputs
  input                                 op_setflag_i,
  input                                 flag_i, // feedback from ctrl (for cmov)

  // multi-clock instruction related inputs
  //  ## multiplier inputs
  input                                 op_mul_i,
  //  ## division inputs
  input                                 op_div_i,
  input                                 op_div_signed_i,
  input                                 op_div_unsigned_i,
  //  ## FPU-32 arithmetic part
  input         [`OR1K_FPUOP_WIDTH-1:0] op_fp32_arith_i,
  input       [`OR1K_FPCSR_RM_SIZE-1:0] fpu_round_mode_i,
  //  ## FPU-32 comparison part
  input         [`OR1K_FPUOP_WIDTH-1:0] op_fp32_cmp_i,
  //  ## MFSPR
  input                                 ctrl_mfspr_rdy_i,
  input      [OPTION_OPERAND_WIDTH-1:0] mfspr_dat_i,
  //  ## MSYNC related controls
  input                                 msync_done_i,
  //  ## LSU related inputs
  input                                 lsu_valid_i,
  input                                 wb_lsu_rdy_i,
  input      [OPTION_OPERAND_WIDTH-1:0] wb_lsu_result_i,

  // EXCEPTIONS related input
  //  ## instruction is interruptable
  input                                 exec_excepts_en_i,
  //  ## RFE processing
  input                                 exec_op_rfe_i,
  //  ## input exceptions
  input                                 exec_except_ibus_err_i,
  input                                 exec_except_ipagefault_i,
  input                                 exec_except_itlb_miss_i,
  input                                 exec_except_ibus_align_i,
  input                                 exec_except_illegal_i,
  input                                 exec_except_syscall_i,
  input                                 exec_except_trap_i,
  input                                 lsu_except_dbus_err_i,
  input                                 lsu_except_dpagefault_i,
  input                                 lsu_except_dtlb_miss_i,
  input                                 lsu_except_dbus_align_i,
  input                                 lsu_excepts_i,

  // ALU results
  output     [OPTION_OPERAND_WIDTH-1:0] exec_lsu_adr_o,  // not latched, address to LSU

  // EXEC ready flag
  output                                exec_valid_o,

  // WB outputs
  output     [OPTION_OPERAND_WIDTH-1:0] wb_result_o,
  //  ## integer comparison result
  output reg                            wb_int_flag_set_o,
  output reg                            wb_int_flag_clear_o,
  //  ## carry output
  output reg                            wb_carry_set_o,
  output reg                            wb_carry_clear_o,
  //  ## overflow output
  output reg                            wb_overflow_set_o,
  output reg                            wb_overflow_clear_o,
  //  ## FPU-32 arithmetic exceptions
  output        [`OR1K_FPCSR_WIDTH-1:0] wb_fp32_arith_fpcsr_o,
  //  ## FPU-32 comparison result
  output                                wb_fp32_flag_set_o,
  output                                wb_fp32_flag_clear_o,
  output        [`OR1K_FPCSR_WIDTH-1:0] wb_fp32_cmp_fpcsr_o,
  //  ## instruction related information
  output reg [OPTION_OPERAND_WIDTH-1:0] pc_wb_o,
  output reg                            wb_delay_slot_o,
  output reg [OPTION_RF_ADDR_WIDTH-1:0] wb_rfd_adr_o,
  output reg                            wb_rf_wb_o,
  //  ## RFE processing
  output reg                            wb_op_rfe_o,
  //  ## output exceptions
  output reg                            wb_except_ibus_err_o,
  output reg                            wb_except_ipagefault_o,
  output reg                            wb_except_itlb_miss_o,
  output reg                            wb_except_ibus_align_o,
  output reg                            wb_except_illegal_o,
  output reg                            wb_except_syscall_o,
  output reg                            wb_except_trap_o,
  output reg                            wb_except_dbus_o,
  output reg                            wb_except_dpagefault_o,
  output reg                            wb_except_dtlb_miss_o,
  output reg                            wb_except_align_o,
  output reg                            wb_excepts_en_o
);

  localparam  EXEDW = OPTION_OPERAND_WIDTH; // short name


  wire [EXEDW-1:0] op_a = rfa_i;
  wire [EXEDW-1:0] op_b = immediate_sel_i ? immediate_i : rfb_i;


  //------------------//
  // Adder/subtractor //
  //------------------//
  // outputs
  wire             adder_carryout;
  wire [EXEDW-1:0] adder_result;
  // inputs
  wire [EXEDW-1:0] b_mux = adder_do_sub_i ? (~op_b) : op_b;
  wire carry_in = adder_do_sub_i | (adder_do_carry_i & carry_i);
  // Adder
  assign {adder_carryout, adder_result} =
           op_a + b_mux + {{(EXEDW-1){1'b0}},carry_in};
  // result sign
  wire adder_result_sign = adder_result[EXEDW-1];
  // signed overflow detection
  // Input signs are same and result sign is different to input signs
  wire adder_s_ovf =
         (op_a[EXEDW-1] == b_mux[EXEDW-1]) &
         (op_a[EXEDW-1] ^ adder_result[EXEDW-1]);
  // unsigned overflow detection
  wire adder_u_ovf = adder_carryout;


  //------------------//
  // Comparison logic //
  //------------------//
  wire a_eq_b  = (op_a == op_b); // Equal compare
  wire a_lts_b = (adder_result_sign ^ adder_s_ovf); // Signed compare (sign != ovf)
  wire a_ltu_b = ~adder_carryout; // Unsigned compare
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


  //------//
  // FFL1 //
  //------//
  wire [EXEDW-1:0] ffl1_result;
  assign ffl1_result = (opc_alu_secondary_i[2]) ?
           (op_a[31] ? 32 : op_a[30] ? 31 : op_a[29] ? 30 :
            op_a[28] ? 29 : op_a[27] ? 28 : op_a[26] ? 27 :
            op_a[25] ? 26 : op_a[24] ? 25 : op_a[23] ? 24 :
            op_a[22] ? 23 : op_a[21] ? 22 : op_a[20] ? 21 :
            op_a[19] ? 20 : op_a[18] ? 19 : op_a[17] ? 18 :
            op_a[16] ? 17 : op_a[15] ? 16 : op_a[14] ? 15 :
            op_a[13] ? 14 : op_a[12] ? 13 : op_a[11] ? 12 :
            op_a[10] ? 11 : op_a[9] ? 10 : op_a[8] ? 9 :
            op_a[7] ? 8 : op_a[6] ? 7 : op_a[5] ? 6 : op_a[4] ? 5 :
            op_a[3] ? 4 : op_a[2] ? 3 : op_a[1] ? 2 : op_a[0] ? 1 : 0 ) :
           (op_a[0] ? 1 : op_a[1] ? 2 : op_a[2] ? 3 : op_a[3] ? 4 :
            op_a[4] ? 5 : op_a[5] ? 6 : op_a[6] ? 7 : op_a[7] ? 8 :
            op_a[8] ? 9 : op_a[9] ? 10 : op_a[10] ? 11 : op_a[11] ? 12 :
            op_a[12] ? 13 : op_a[13] ? 14 : op_a[14] ? 15 :
            op_a[15] ? 16 : op_a[16] ? 17 : op_a[17] ? 18 :
            op_a[18] ? 19 : op_a[19] ? 20 : op_a[20] ? 21 :
            op_a[21] ? 22 : op_a[22] ? 23 : op_a[23] ? 24 :
            op_a[24] ? 25 : op_a[25] ? 26 : op_a[26] ? 27 :
            op_a[27] ? 28 : op_a[28] ? 29 : op_a[29] ? 30 :
            op_a[30] ? 31 : op_a[31] ? 32 : 0);


  //----------------//
  // Barrel shifter //
  //----------------//
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
  assign shift_lsw = op_sll ? reverse(op_a) : op_a;
  assign shift_msw = op_sra ? {EXEDW{op_a[EXEDW-1]}} :
                     op_ror ? op_a : {EXEDW{1'b0}};

  assign shift_right = {shift_msw, shift_lsw} >> op_b[4:0];
  assign shift_result = op_sll ? reverse(shift_right) : shift_right;


  //------------------//
  // Conditional move //
  //------------------//
  wire [EXEDW-1:0] cmov_result;
  assign cmov_result = flag_i ? op_a : op_b;


  //--------------------//
  // Logical operations //
  //--------------------//
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
  end

  // Extract the result, bit-for-bit, from the look-up-table
  integer i;
  always @(*)
    for (i = 0; i < EXEDW; i=i+1) begin
      logic_result[i] = logic_lut[{op_a[i], op_b[i]}];
    end

  assign op_logic = |logic_lut;


  //------------------------------------------------------------------//
  // Muxing and registering 1-clk results and integer comparison flag //
  //------------------------------------------------------------------//
  wire [EXEDW-1:0] alu_1clk_result_mux = op_shift_i ? shift_result      :
                                         op_ffl1_i  ? ffl1_result       :
                                         op_add_i   ? adder_result      :
                                         op_logic   ? logic_result      :
                                         op_cmov_i  ? cmov_result       :
                                         op_movhi_i ? immediate_i       :
                                         op_jal_i   ? exec_jal_result_i : // for GPR[9]
                                                      {EXEDW{1'b0}};
  //  registering output for 1-clock operations
  reg [EXEDW-1:0] wb_alu_1clk_result;
  reg             wb_alu_1clk_rdy;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_alu_1clk_result <= {EXEDW{1'b0}};
    else if (exec_insn_1clk_i & padv_wb_i)
      wb_alu_1clk_result <= alu_1clk_result_mux;
  end // posedge clock
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_alu_1clk_rdy <= 1'b0;
    else if (pipeline_flush_i)
      wb_alu_1clk_rdy <= wb_alu_1clk_rdy;
    else if (padv_wb_i)
      wb_alu_1clk_rdy <= exec_insn_1clk_i;
  end // @clock

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
      if (op_setflag_i) begin
        wb_int_flag_set_o   <= flag_set;
        wb_int_flag_clear_o <= ~flag_set;
      end
      else begin
        wb_int_flag_set_o   <= 1'b0;
        wb_int_flag_clear_o <= 1'b0;
      end // set-flag-op / not
    end // wb advance
  end // @clock



  //-------------------//
  // 32-bit multiplier //
  //-------------------//
  localparam MULHDW = (EXEDW >> 1);

  // algorithm:
  //   AlBl[dw-1:0] = A[hdw-1:0] * B[hdw-1:0];
  //   AhBl[dw-1:0] = A[dw-1:hdw] * B[hdw-1:0];
  //   BhAl[dw-1:0] = B[dw-1:hdw] * A[hdw-1:0];
  //   Sum[dw-1:0]  = {BhAl[hdw-1:0],{hdw{0}}} +
  //                  {AlBl[hdw-1:0],{hdw{0}}} +
  //                  AlBl;

  wire mul_valid; // valid flag is 1-clock ahead of latching for WB
  wire mul_adv = ~mul_valid | padv_wb_i; // advance multiplier pipe

  // stage #1: register inputs & split them on halfed parts
  reg [MULHDW-1:0] mul_s1_al;
  reg [MULHDW-1:0] mul_s1_bl;
  reg [MULHDW-1:0] mul_s1_ah;
  reg [MULHDW-1:0] mul_s1_bh;
  //  registering
  always @(posedge clk) begin
    if (op_mul_i & mul_adv) begin
      mul_s1_al <= op_a[MULHDW-1:0];
      mul_s1_bl <= op_b[MULHDW-1:0];
      mul_s1_ah <= op_a[EXEDW-1:MULHDW];
      mul_s1_bh <= op_b[EXEDW-1:MULHDW];
    end
  end // posedge clock
  //  ready flag
  reg mul_s1_rdy;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      mul_s1_rdy <= 1'b0;
    else if (pipeline_flush_i)
      mul_s1_rdy <= 1'b0;
    else if (mul_adv)
      mul_s1_rdy <= op_mul_i;
  end // posedge clock

  // stage #2: partial products
  reg [EXEDW-1:0] mul_s2_albl;
  reg [EXEDW-1:0] mul_s2_ahbl;
  reg [EXEDW-1:0] mul_s2_bhal;
  //  registering
  always @(posedge clk) begin
    if (mul_s1_rdy & mul_adv) begin
      mul_s2_albl <= mul_s1_al * mul_s1_bl;
      mul_s2_ahbl <= mul_s1_ah * mul_s1_bl;
      mul_s2_bhal <= mul_s1_bh * mul_s1_al;
    end
  end // posedge clock
  //  ready flag
  reg mul_s2_rdy;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      mul_s2_rdy <= 1'b0;
    else if (pipeline_flush_i)
      mul_s2_rdy <= 1'b0;
    else if (mul_adv)
      mul_s2_rdy <= mul_s1_rdy;
  end // posedge clock
  // valid flag is 1-clock ahead of latching for WB
  assign mul_valid = mul_s2_rdy;

  // stage #3: result
  wire [EXEDW-1:0] mul_s3t_sum;
  assign mul_s3t_sum = {mul_s2_bhal[MULHDW-1:0],{MULHDW{1'b0}}} +
                       {mul_s2_ahbl[MULHDW-1:0],{MULHDW{1'b0}}} +
                        mul_s2_albl;
  //  registering
  reg [EXEDW-1:0] wb_mul_result;
  reg             wb_mul_rdy;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_mul_result <= {EXEDW{1'b0}};
    else if (mul_valid & padv_wb_i)
      wb_mul_result <= mul_s3t_sum;
  end // posedge clock
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_mul_rdy <= 1'b0;
    else if (pipeline_flush_i)
      wb_mul_rdy <= wb_mul_rdy;
    else if (padv_wb_i)
      wb_mul_rdy <= mul_valid;
  end // @clock



  //----------------//
  // 32-bit divider //
  //----------------//
  reg       [5:0] div_count;
  reg [EXEDW-1:0] div_n;
  reg [EXEDW-1:0] div_d;
  reg [EXEDW-1:0] div_r;
  wire  [EXEDW:0] div_sub;
  reg             div_signed, div_unsigned;
  reg             div_neg;
  reg             div_valid;
  reg             div_by_zero;

  assign div_sub = {div_r[EXEDW-2:0],div_n[EXEDW-1]} - div_d;

  // Cycle counter
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      div_valid <= 1'b0;
      div_count <= 6'd0;
    end
    if (padv_decode_i | pipeline_flush_i) begin // reset @ new decode data
      div_valid <= 1'b0;
      div_count <= 6'd0;
    end
    else if (op_div_i) begin
      div_valid <= 1'b0;
      div_count <= EXEDW;
    end
    else if (|div_count) begin
      if (div_count == 6'd1)
        div_valid <= 1'b1;
      else if (~div_valid)
        div_count <= div_count - 6'd1;
    end
  end // @clock

  always @(posedge clk) begin
    if (op_div_i) begin
      div_n        <= rfa_i;
      div_d        <= rfb_i;
      div_r        <= 0;
      div_neg      <= 1'b0;
      div_by_zero  <= ~(|rfb_i);
      div_signed   <= op_div_signed_i;
      div_unsigned <= op_div_unsigned_i;
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
    else if (~div_valid) begin
      if (~div_sub[EXEDW]) begin // div_sub >= 0
        div_r <= div_sub[EXEDW-1:0];
        div_n <= {div_n[EXEDW-2:0], 1'b1};
      end
      else begin                 // div_sub < 0
        div_r <= {div_r[EXEDW-2:0],div_n[EXEDW-1]};
        div_n <= {div_n[EXEDW-2:0], 1'b0};
      end
    end // ~done
  end // @clock

  wire [EXEDW-1:0] div_result = div_neg ? ~div_n + 1 : div_n;
  
  //  registering
  reg [EXEDW-1:0] wb_div_result;
  reg             wb_div_rdy;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_div_result <= {EXEDW{1'b0}};
    else if (div_valid & padv_wb_i)
      wb_div_result <= div_result;
  end // posedge clock
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_div_rdy <= 1'b0;
    else if (pipeline_flush_i)
      wb_div_rdy <= wb_div_rdy;
    else if (padv_wb_i)
      wb_div_rdy <= div_valid;
  end // @clock



  //-------------//
  // FPU related //
  //-------------//
  //  arithmetic part interface
  wire        fp32_arith_valid;
  wire [31:0] wb_fp32_arith_res;
  wire        wb_fp32_arith_rdy;
  //  instance
  generate
    /* verilator lint_off WIDTH */
    if (FEATURE_FPU!="NONE") begin :  fpu_alu_ena
    /* verilator lint_on WIDTH */
      pfpu32_top_marocchino  u_pfpu32
      (
        // clock & reset
        .clk                    (clk),
        .rst                    (rst),
        // pipeline control
        .flush_i                (pipeline_flush_i),
        .padv_wb_i              (padv_wb_i),
        // Operands
        .rfa_i                  (rfa_i),
        .rfb_i                  (rfb_i),
        // FPU-32 arithmetic part
        .op_arith_i             (op_fp32_arith_i),
        .round_mode_i           (fpu_round_mode_i),
        .fp32_arith_valid_o     (fp32_arith_valid),      // WB-latching ahead arithmetic ready flag
        .wb_fp32_arith_res_o    (wb_fp32_arith_res),     // arithmetic result
        .wb_fp32_arith_rdy_o    (wb_fp32_arith_rdy),     // arithmetic ready flag
        .wb_fp32_arith_fpcsr_o  (wb_fp32_arith_fpcsr_o), // arithmetic exceptions
        // FPU-32 comparison part
        .op_cmp_i               (op_fp32_cmp_i),
        .wb_fp32_flag_set_o     (wb_fp32_flag_set_o),   // comparison result
        .wb_fp32_flag_clear_o   (wb_fp32_flag_clear_o), // comparison result
        .wb_fp32_cmp_fpcsr_o    (wb_fp32_cmp_fpcsr_o)   // comparison exceptions
      );
    end
    else begin :  fpu_alu_none
      // arithmetic part
      assign fp32_arith_valid      =  1'b0;
      assign wb_fp32_arith_res     = 32'd0;
      assign wb_fp32_arith_rdy     =  1'b0;
      assign wb_fp32_arith_fpcsr_o = {`OR1K_FPCSR_WIDTH{1'b0}};
      // comparison part
      assign wb_fp32_flag_set_o    =  1'b0;
      assign wb_fp32_flag_clear_o  =  1'b0;
      assign wb_fp32_cmp_fpcsr_o   = {`OR1K_FPCSR_WIDTH{1'b0}};
    end // fpu_ena/fpu_none
  endgenerate // FPU related



  //-----------------//
  // Address for LSU //
  //-----------------//
  assign exec_lsu_adr_o = adder_result; // lsu address (not latched)



  //-------------//
  // Stall logic //
  //-------------//
  assign exec_valid_o =
    exec_insn_1clk_i | div_valid | mul_valid | fp32_arith_valid |
    lsu_valid_i | lsu_excepts_i | msync_done_i;



  //-----------------------------//
  // WB multiplexors and latches //
  //-----------------------------//
  // combined output
  assign wb_result_o = ctrl_mfspr_rdy_i  ? mfspr_dat_i :
                       wb_lsu_rdy_i      ? wb_lsu_result_i :
                       wb_alu_1clk_rdy   ? wb_alu_1clk_result :
                       wb_mul_rdy        ? wb_mul_result :
                       wb_div_rdy        ? wb_div_result :
                       wb_fp32_arith_rdy ? wb_fp32_arith_res :
                                           {EXEDW{1'b0}};

  // Overflow flag generation
  // latched integer comparison result for WB
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      wb_overflow_set_o   <= 1'b0;
      wb_overflow_clear_o <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      wb_overflow_set_o   <= 1'b0;
      wb_overflow_clear_o <= 1'b0;
    end
    else if (padv_wb_i) begin
      wb_overflow_set_o   <= (op_add_i & adder_s_ovf) |
                             (div_valid & div_signed & div_by_zero);
      wb_overflow_clear_o <= (op_add_i & (~adder_s_ovf)) |
                             (div_valid & div_signed & (~div_by_zero));
    end // wb advance
  end // @clock

  // Carry flag generation
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      wb_carry_set_o   <= 1'b0;
      wb_carry_clear_o <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      wb_carry_set_o   <= 1'b0;
      wb_carry_clear_o <= 1'b0;
    end
    else if (padv_wb_i) begin
      wb_carry_set_o   <= (op_add_i & adder_u_ovf) |
                          (div_valid & div_unsigned & div_by_zero);
      wb_carry_clear_o <= (op_add_i & (~adder_u_ovf)) |
                          (div_valid & div_unsigned & (~div_by_zero));
    end // wb advance
  end // @clock


  // write back request
  wire pipe_excepts = exec_excepts_en_i &
                      (exec_except_ibus_err_i  | exec_except_ipagefault_i |
                       exec_except_itlb_miss_i | exec_except_ibus_align_i |
                       exec_except_illegal_i   | exec_except_syscall_i    |
                       exec_except_trap_i      | lsu_excepts_i);
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      wb_rf_wb_o      <= 1'b0;
      wb_delay_slot_o <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      wb_rf_wb_o      <= 1'b0;
      wb_delay_slot_o <= 1'b0;
    end
    else if (padv_wb_i) begin
      wb_rf_wb_o      <= exec_rf_wb_i & (~pipe_excepts);
      wb_delay_slot_o <= exec_delay_slot_i;
    end
  end // @clock

  // address of destination register & PC
  always @(posedge clk) begin
    if (padv_wb_i & 
        (~pipeline_flush_i) & (~exec_bubble_i)) begin
      wb_rfd_adr_o <= exec_rfd_adr_i;
      pc_wb_o      <= pc_exec_i;
    end 
  end // @clock


  // EXCEPTIONS & RFE
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      wb_except_ibus_err_o   <= 1'b0;
      wb_except_ipagefault_o <= 1'b0;
      wb_except_itlb_miss_o  <= 1'b0;
      wb_except_ibus_align_o <= 1'b0;
      wb_except_illegal_o    <= 1'b0;
      wb_except_syscall_o    <= 1'b0;
      wb_except_trap_o       <= 1'b0;
      wb_except_dbus_o       <= 1'b0;
      wb_except_dpagefault_o <= 1'b0;
      wb_except_dtlb_miss_o  <= 1'b0;
      wb_except_align_o      <= 1'b0;
      wb_excepts_en_o        <= 1'b0;
      // RFE
      wb_op_rfe_o            <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      wb_except_ibus_err_o   <= 1'b0;
      wb_except_ipagefault_o <= 1'b0;
      wb_except_itlb_miss_o  <= 1'b0;
      wb_except_ibus_align_o <= 1'b0;
      wb_except_illegal_o    <= 1'b0;
      wb_except_syscall_o    <= 1'b0;
      wb_except_trap_o       <= 1'b0;
      wb_except_dbus_o       <= 1'b0;
      wb_except_dpagefault_o <= 1'b0;
      wb_except_dtlb_miss_o  <= 1'b0;
      wb_except_align_o      <= 1'b0;
      wb_excepts_en_o        <= 1'b0;
      // RFE
      wb_op_rfe_o            <= 1'b0;
    end
    else if (padv_wb_i) begin
      wb_except_ibus_err_o   <= exec_except_ibus_err_i;
      wb_except_ipagefault_o <= exec_except_ipagefault_i;
      wb_except_itlb_miss_o  <= exec_except_itlb_miss_i;
      wb_except_ibus_align_o <= exec_except_ibus_align_i;
      wb_except_illegal_o    <= exec_except_illegal_i;
      wb_except_syscall_o    <= exec_except_syscall_i;
      wb_except_trap_o       <= exec_except_trap_i;
      wb_except_dbus_o       <= lsu_except_dbus_err_i;
      wb_except_dpagefault_o <= lsu_except_dpagefault_i;
      wb_except_dtlb_miss_o  <= lsu_except_dtlb_miss_i;
      wb_except_align_o      <= lsu_except_dbus_align_i;
      wb_excepts_en_o        <= exec_excepts_en_i;
      // RFE
      wb_op_rfe_o            <= exec_op_rfe_i;
    end
  end // @clock

endmodule // mor1kx_execute_marocchino
