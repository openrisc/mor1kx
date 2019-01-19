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


//-------------------//
// 32-bit multiplier //
//-------------------//

module mor1kx_multiplier_marocchino
#(
  parameter OPTION_OPERAND_WIDTH = 32
)
(
  // clocks and resets
  input                                 cpu_clk,

  // pipeline control signal in
  input                                 pipeline_flush_i,
  input                                 padv_wrbk_i,
  input                                 grant_wrbk_to_mul_i,

  // input operands from  reservation station
  input      [OPTION_OPERAND_WIDTH-1:0] exec_mul_a1_i,
  input      [OPTION_OPERAND_WIDTH-1:0] exec_mul_b1_i,

  //  other inputs/outputs
  input                                 exec_op_mul_i,
  output                                imul_taking_op_o,
  output reg                            mul_valid_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] wrbk_mul_result_o
);

  localparam MULDW  = OPTION_OPERAND_WIDTH; // short name
  localparam MULHDW = (OPTION_OPERAND_WIDTH >> 1);

  // algorithm:
  //   AlBl[dw-1:0] = A[hdw-1:0] * B[hdw-1:0];
  //   AhBl[dw-1:0] = A[dw-1:hdw] * B[hdw-1:0];
  //   BhAl[dw-1:0] = B[dw-1:hdw] * A[hdw-1:0];
  //   Sum[dw-1:0]  = {BhAl[hdw-1:0],{hdw{0}}} +
  //                  {AhBl[hdw-1:0],{hdw{0}}} +
  //                  AlBl;

  // multiplier controls
  //  ## multiplier stage ready flags
  reg    mul_s1_rdy;
  reg    wrbk_mul_miss_r;
  //  ## stage busy signals
  wire   mul_s1_busy = mul_s1_rdy & wrbk_mul_miss_r;
  //  ## stage advance signals
  wire   mul_adv_s1  = exec_op_mul_i & ~mul_s1_busy;

  // integer multiplier is taking operands
  assign imul_taking_op_o = mul_adv_s1;


  // stage #1
  // --- split input operands ---
  wire [MULHDW-1:0] s1t_mul_al = exec_mul_a1_i[MULHDW-1:0];
  wire [MULHDW-1:0] s1t_mul_bl = exec_mul_b1_i[MULHDW-1:0];
  wire [MULHDW-1:0] s1t_mul_ah = exec_mul_a1_i[MULDW-1:MULHDW];
  wire [MULHDW-1:0] s1t_mul_bh = exec_mul_b1_i[MULDW-1:MULHDW];
  // --- output partial products ---
  reg  [MULDW-1:0] s1o_mul_albl;
  reg  [MULDW-1:0] s1o_mul_bhal;
  reg  [MULDW-1:0] s1o_mul_ahbl;
  //  registering
  always @(posedge cpu_clk) begin
    if (mul_adv_s1) begin
      s1o_mul_albl <= s1t_mul_al * s1t_mul_bl;
      s1o_mul_bhal <= s1t_mul_bh * s1t_mul_al;
      s1o_mul_ahbl <= s1t_mul_ah * s1t_mul_bl;
    end
  end // @clock
  //  ready flag
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      mul_s1_rdy <= 1'b0;
    else if (mul_adv_s1)
      mul_s1_rdy <= 1'b1;
    else if (~wrbk_mul_miss_r)
      mul_s1_rdy <= 1'b0;
  end // @clock
  //  valid flag
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      mul_valid_o <= 1'b0;
    else if (mul_adv_s1)
      mul_valid_o <= 1'b1;
    else if (padv_wrbk_i & grant_wrbk_to_mul_i)
      mul_valid_o <= wrbk_mul_miss_r ? mul_s1_rdy : 1'b0;
  end // @clock


  // stage #2:
  //  --- add partial products ---
  wire [MULHDW-1:0] s2t_mul_acc;
  assign s2t_mul_acc = s1o_mul_albl[MULDW-1:MULHDW] +
                       s1o_mul_bhal[MULHDW-1:0] +
                       s1o_mul_ahbl[MULHDW-1:0];
  //  --- combine whole result ---
  wire [MULDW-1:0] s2t_mul_result = {s2t_mul_acc, s1o_mul_albl[MULHDW-1:0]};


  // padv-wrbk decoupling
  //  ## Write-Back-miss flag
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      wrbk_mul_miss_r <= 1'b0;
    else if (padv_wrbk_i & grant_wrbk_to_mul_i)
      wrbk_mul_miss_r <= 1'b0;
    else if (~wrbk_mul_miss_r)
      wrbk_mul_miss_r <= mul_s1_rdy;
  end // @clock
  //  ## Write-Back-miss pending result
  reg [MULDW-1:0] mul_result_p;
  // ---
  always @(posedge cpu_clk) begin
    if (~wrbk_mul_miss_r)
      mul_result_p <= s2t_mul_result;
  end // @clock
  //  Write-Back-registering
  wire [MULDW-1:0] mul_result_m = wrbk_mul_miss_r ? mul_result_p : s2t_mul_result;
  // ---
  always @(posedge cpu_clk) begin
    if (padv_wrbk_i) begin
      if (grant_wrbk_to_mul_i)
        wrbk_mul_result_o <= mul_result_m;
      else
        wrbk_mul_result_o <= {MULDW{1'b0}};
    end
  end // @clock

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
  input                                 cpu_clk,

  // pipeline control signal in
  input                                 pipeline_flush_i,
  input                                 padv_wrbk_i,
  input                                 grant_wrbk_to_div_i,

  // input data from reservation station
  input      [OPTION_OPERAND_WIDTH-1:0] exec_div_a1_i,
  input      [OPTION_OPERAND_WIDTH-1:0] exec_div_b1_i,

  // division command
  input                                 exec_op_div_i,
  input                                 exec_op_div_signed_i,
  input                                 exec_op_div_unsigned_i,

  // division engine state
  output                                idiv_taking_op_o,
  output                                div_valid_o,

  // write back
  //  # update carry flag by division
  output reg                            wrbk_div_carry_set_o,
  output reg                            wrbk_div_carry_clear_o,
  //  # update overflow flag by division
  output reg                            wrbk_div_overflow_set_o,
  output reg                            wrbk_div_overflow_clear_o,
  //  # generate overflow exception by division
  input                                 except_overflow_enable_i,
  output                                exec_except_overflow_div_o,
  output reg                            wrbk_except_overflow_div_o,
  //  # division result
  output reg [OPTION_OPERAND_WIDTH-1:0] wrbk_div_result_o
);

  localparam DIVDW        = OPTION_OPERAND_WIDTH; // short name
  localparam LOG2_DIVDW_2 = 4; // ceil(log2(DIVDW/2)): size of iteration counter

  // common interface for both SERIAL/SRT4 divisors
  wire [DIVDW-1:0] s3t_div_result;
  wire             s3o_dbz;
  reg              s3o_div_signed, s3o_div_unsigned;
  wire             div_s3_rdy;
  reg              wrbk_div_miss_r;

  // divider controls
  //  ## iterations counter and processing flag
  reg [5:0] div_count;
  reg       div_proc_r;
  //  ## valid (registered, similar to multiplier)
  reg       div_s3_rdy_r;
  reg       div_valid_r;

  //  ## dvisor is busy
  wire   div_s3_busy = div_proc_r | (div_s3_rdy_r & wrbk_div_miss_r);
  //  ## start division
  assign idiv_taking_op_o = exec_op_div_i & (~div_s3_busy);


  // division controller
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i) begin
      div_s3_rdy_r <= 1'b0;
      div_proc_r   <= 1'b0;
      div_count    <= 6'd0;
    end
    else if (idiv_taking_op_o) begin
      div_s3_rdy_r <= 1'b0;
      div_proc_r   <= 1'b1;
      div_count    <= DIVDW;
    end
    else if (div_s3_rdy_r & (~wrbk_div_miss_r)) begin
      div_s3_rdy_r <= 1'b0;
      div_proc_r   <= 1'b0;
      div_count    <= 6'd0;
    end
    else if (div_proc_r) begin
      if (div_count == 6'd1) begin
        div_s3_rdy_r <= 1'b1;
        div_proc_r   <= 1'b0;
      end
      div_count <= div_count - 6'd1;
    end
  end // @clock


  // valid flag to pipeline control
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      div_valid_r <= 1'b0;
    else if (div_proc_r & (div_count == 6'd1)) // sync to "div_s3_rdy_r"
      div_valid_r <= 1'b1;
    else if (padv_wrbk_i & grant_wrbk_to_div_i)
      div_valid_r <= wrbk_div_miss_r ? div_s3_rdy_r : 1'b0;
  end // @clock

  //  ## result valid
  assign div_s3_rdy  = div_s3_rdy_r;
  assign div_valid_o = div_valid_r;


  // regs of divider
  reg [DIVDW-1:0] div_n;
  reg [DIVDW-1:0] div_d;
  reg [DIVDW-1:0] div_r;
  reg             div_neg;
  reg             dbz_r;

  // signums of input operands
  wire op_div_sign_a = exec_div_a1_i[DIVDW-1] & exec_op_div_signed_i;
  wire op_div_sign_b = exec_div_b1_i[DIVDW-1] & exec_op_div_signed_i;

  // partial reminder
  wire [DIVDW:0] div_sub = {div_r[DIVDW-2:0],div_n[DIVDW-1]} - div_d;

  always @(posedge cpu_clk) begin
    if (idiv_taking_op_o) begin
      // Convert negative operands in the case of signed division.
      // If only one of the operands is negative, the result is
      // converted back to negative later on
      div_n   <= (exec_div_a1_i ^ {DIVDW{op_div_sign_a}}) + {{(DIVDW-1){1'b0}},op_div_sign_a};
      div_d   <= (exec_div_b1_i ^ {DIVDW{op_div_sign_b}}) + {{(DIVDW-1){1'b0}},op_div_sign_b};
      div_r   <= {DIVDW{1'b0}};
      div_neg <= (op_div_sign_a ^ op_div_sign_b);
      dbz_r   <= (exec_div_b1_i == {DIVDW{1'b0}});
      s3o_div_signed   <= exec_op_div_signed_i;
      s3o_div_unsigned <= exec_op_div_unsigned_i;
    end
    else if (~div_valid_r) begin
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

  assign s3t_div_result = (div_n ^ {DIVDW{div_neg}}) + {{(DIVDW-1){1'b0}},div_neg};
  assign s3o_dbz = dbz_r;


  /**** DIV Write Back ****/

  // Write-Back-miss registers
  //  ## Write-Back-miss flag
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      wrbk_div_miss_r <= 1'b0;
    else if (padv_wrbk_i & grant_wrbk_to_div_i)
      wrbk_div_miss_r <= 1'b0;
    else if (~wrbk_div_miss_r)
      wrbk_div_miss_r <= div_s3_rdy;
  end // @clock

  //  # update carry flag by division
  wire div_carry_set      = s3o_div_unsigned &   s3o_dbz;
  wire div_carry_clear    = s3o_div_unsigned & (~s3o_dbz);

  //  # update overflow flag by division
  wire div_overflow_set   = s3o_div_signed &   s3o_dbz;
  wire div_overflow_clear = s3o_div_signed & (~s3o_dbz);

  //  ## Write-Back-miss pending result
  reg [DIVDW-1:0] div_result_p;
  reg             div_carry_set_p;
  reg             div_carry_clear_p;
  reg             div_overflow_set_p;
  reg             div_overflow_clear_p;
  // ---
  always @(posedge cpu_clk) begin
    if (~wrbk_div_miss_r) begin
      div_result_p         <= s3t_div_result;
      div_carry_set_p      <= div_carry_set;
      div_carry_clear_p    <= div_carry_clear;
      div_overflow_set_p   <= div_overflow_set;
      div_overflow_clear_p <= div_overflow_clear;
    end
  end // @clock

  //  # generate overflow exception by division
  wire   mux_except_overflow_div    = except_overflow_enable_i & (wrbk_div_miss_r ? div_overflow_set_p : div_overflow_set);
  assign exec_except_overflow_div_o = grant_wrbk_to_div_i & mux_except_overflow_div;

  //  Write-Back-registering result
  wire [DIVDW-1:0] wrbk_div_result_m = wrbk_div_miss_r ? div_result_p : s3t_div_result;
  // ---
  always @(posedge cpu_clk) begin
    if (padv_wrbk_i) begin
      if (grant_wrbk_to_div_i)
        wrbk_div_result_o <= wrbk_div_result_m;
      else
        wrbk_div_result_o <= {DIVDW{1'b0}};
    end
  end // @clock

  // Write-Back-latchers
  always @(posedge cpu_clk) begin
    if (padv_wrbk_i & grant_wrbk_to_div_i) begin
      //  # update carry flag by division
      wrbk_div_carry_set_o        <= wrbk_div_miss_r ? div_carry_set_p : div_carry_set;
      wrbk_div_carry_clear_o      <= wrbk_div_miss_r ? div_carry_clear_p : div_carry_clear;
      //  # update overflow flag by division
      wrbk_div_overflow_set_o     <= wrbk_div_miss_r ? div_overflow_set_p : div_overflow_set;
      wrbk_div_overflow_clear_o   <= wrbk_div_miss_r ? div_overflow_clear_p : div_overflow_clear;
      //  # generate overflow exception by division
      wrbk_except_overflow_div_o  <= mux_except_overflow_div;
    end
    else begin
      //  # update carry flag by division
      wrbk_div_carry_set_o        <= 1'b0;
      wrbk_div_carry_clear_o      <= 1'b0;
      //  # update overflow flag by division
      wrbk_div_overflow_set_o     <= 1'b0;
      wrbk_div_overflow_clear_o   <= 1'b0;
      //  # generate overflow exception by division
      wrbk_except_overflow_div_o  <= 1'b0;
    end
  end // @clock

endmodule // mor1kx_divider_marocchino



//-----------------------------------------------//
// 1-clock operations including FP-32 comparison //
//-----------------------------------------------//

module mor1kx_exec_1clk_marocchino
#(
  parameter OPTION_OPERAND_WIDTH = 32
)
(
  // clocks and resets
  input                                 cpu_clk,

  // pipeline control signal in
  input                                 pipeline_flush_i,
  input                                 padv_wrbk_i,
  input                                 grant_wrbk_to_1clk_i,
  output                                taking_1clk_op_o,
  output                                op_1clk_valid_o,

  // flags for in-1clk-unit forwarding multiplexors
  input                                 exec_1clk_ff_d1a1_i,
  input                                 exec_1clk_ff_d1b1_i,

  // input operands A and B with forwarding from Write-Back
  input      [OPTION_OPERAND_WIDTH-1:0] exec_1clk_a1_i,
  input      [OPTION_OPERAND_WIDTH-1:0] exec_1clk_b1_i,

  // 1-clock instruction auxiliaries
  input                                 carry_i, // feedback from ctrl
  input                                 flag_i, // feedback from ctrl (for cmov)

  // any 1-clock sub-unit
  input                                 exec_op_1clk_i,
  // Reqired flag or carry
  input                                 exec_flag_carry_req_i,
  // adder's inputs
  input                                 exec_op_add_i,
  input                                 exec_adder_do_sub_i,
  input                                 exec_adder_do_carry_i,
  // shift
  input                                 exec_op_shift_i,
  input                           [3:0] exec_opc_shift_i,
  // ffl1
  input                                 exec_op_ffl1_i,
  input                                 exec_opc_ffl1_i,
  // movhi, cmov
  input                                 exec_op_movhi_i,
  input                                 exec_op_cmov_i,
  // extsz
  input                                 exec_op_extsz_i,
  input                           [3:0] exec_opc_extsz_i,
  // logic
  input                                 exec_op_logic_i,
  input                           [3:0] exec_lut_logic_i,
  // Write-Back-latched 1-clock arithmetic result
  output reg [OPTION_OPERAND_WIDTH-1:0] wrbk_1clk_result_o,
  //  # update carry flag by 1clk-operation
  output reg                            wrbk_1clk_carry_set_o,
  output reg                            wrbk_1clk_carry_clear_o,
  //  # update overflow flag by 1clk-operation
  output reg                            wrbk_1clk_overflow_set_o,
  output reg                            wrbk_1clk_overflow_clear_o,
  //  # generate overflow exception by 1clk-operation
  input                                 except_overflow_enable_i,
  output                                exec_except_overflow_1clk_o,
  output reg                            wrbk_except_overflow_1clk_o,

  // integer comparison flag
  input                                 exec_op_setflag_i,
  input      [`OR1K_COMP_OPC_WIDTH-1:0] exec_opc_setflag_i,
  // Write-Back: integer comparison result
  output reg                            wrbk_1clk_flag_set_o,
  output reg                            wrbk_1clk_flag_clear_o
);

  localparam  EXEDW = OPTION_OPERAND_WIDTH; // short name


  //----------------------------//
  // Auxiliary reverse function //
  //----------------------------//
  function [EXEDW-1:0] reverse;
  input [EXEDW-1:0] in;
  integer            i;
  begin
    for (i = 0; i < EXEDW; i=i+1) begin
      reverse[(EXEDW-1)-i] = in[i];
    end
  end
  endfunction


  //-------------------------//
  // In-unit fast forwarding //
  //-------------------------//
  reg  [EXEDW-1:0] ff_1clk_result_r;
  wire [EXEDW-1:0] exec_1clk_a1_m;
  wire [EXEDW-1:0] exec_1clk_b1_m;
  // ---
  assign exec_1clk_a1_m = exec_1clk_ff_d1a1_i ? ff_1clk_result_r : exec_1clk_a1_i;
  assign exec_1clk_b1_m = exec_1clk_ff_d1b1_i ? ff_1clk_result_r : exec_1clk_b1_i;


  //------------------//
  // Adder/subtractor //
  //------------------//
  // outputs
  wire             adder_carryout;
  wire [EXEDW-1:0] adder_result;
  // inputs
  wire [EXEDW-1:0] b_mux = {EXEDW{exec_adder_do_sub_i}} ^ exec_1clk_b1_m; // inverse for l.sub
  wire carry_in = exec_adder_do_sub_i | (exec_adder_do_carry_i & carry_i);
  // Adder
  assign {adder_carryout, adder_result} =
           exec_1clk_a1_m + b_mux + {{(EXEDW-1){1'b0}},carry_in};
  // result sign
  wire adder_result_sign = adder_result[EXEDW-1];
  // signed overflow detection
  // Input signs are same and result sign is different to input signs
  wire adder_s_ovf =
         (exec_1clk_a1_m[EXEDW-1] == b_mux[EXEDW-1]) &
         (exec_1clk_a1_m[EXEDW-1] ^ adder_result[EXEDW-1]);
  // unsigned overflow detection
  wire adder_u_ovf = adder_carryout;


  //------//
  // FFL1 //
  //------//
  // l.fl1
  reg  [5:0] fl1_r;
  reg  [5:0] ff1_r;
  // ---
  wire [EXEDW-1:0] ffl1_result = {{(EXEDW-6){1'b0}}, (exec_opc_ffl1_i ? fl1_r : ff1_r)};
  // ---
  always @(exec_1clk_a1_m) begin
    // synthesis parallel_case
    casez  (exec_1clk_a1_m)
      32'b1???????????????????????????????: fl1_r = 6'd32;
      32'b01??????????????????????????????: fl1_r = 6'd31;
      32'b001?????????????????????????????: fl1_r = 6'd30;
      32'b0001????????????????????????????: fl1_r = 6'd29;
      32'b00001???????????????????????????: fl1_r = 6'd28;
      32'b000001??????????????????????????: fl1_r = 6'd27;
      32'b0000001?????????????????????????: fl1_r = 6'd26;
      32'b00000001????????????????????????: fl1_r = 6'd25;
      32'b000000001???????????????????????: fl1_r = 6'd24;
      32'b0000000001??????????????????????: fl1_r = 6'd23;
      32'b00000000001?????????????????????: fl1_r = 6'd22;
      32'b000000000001????????????????????: fl1_r = 6'd21;
      32'b0000000000001???????????????????: fl1_r = 6'd20;
      32'b00000000000001??????????????????: fl1_r = 6'd19;
      32'b000000000000001?????????????????: fl1_r = 6'd18;
      32'b0000000000000001????????????????: fl1_r = 6'd17;
      32'b00000000000000001???????????????: fl1_r = 6'd16;
      32'b000000000000000001??????????????: fl1_r = 6'd15;
      32'b0000000000000000001?????????????: fl1_r = 6'd14;
      32'b00000000000000000001????????????: fl1_r = 6'd13;
      32'b000000000000000000001???????????: fl1_r = 6'd12;
      32'b0000000000000000000001??????????: fl1_r = 6'd11;
      32'b00000000000000000000001?????????: fl1_r = 6'd10;
      32'b000000000000000000000001????????: fl1_r = 6'd9;
      32'b0000000000000000000000001???????: fl1_r = 6'd8;
      32'b00000000000000000000000001??????: fl1_r = 6'd7;
      32'b000000000000000000000000001?????: fl1_r = 6'd6;
      32'b0000000000000000000000000001????: fl1_r = 6'd5;
      32'b00000000000000000000000000001???: fl1_r = 6'd4;
      32'b000000000000000000000000000001??: fl1_r = 6'd3;
      32'b0000000000000000000000000000001?: fl1_r = 6'd2;
      32'b00000000000000000000000000000001: fl1_r = 6'd1;
      32'b00000000000000000000000000000000: fl1_r = 6'd0;
    endcase
    // synthesis parallel_case
    casez  (exec_1clk_a1_m)
      32'b10000000000000000000000000000000: ff1_r = 6'd32;
      32'b?1000000000000000000000000000000: ff1_r = 6'd31;
      32'b??100000000000000000000000000000: ff1_r = 6'd30;
      32'b???10000000000000000000000000000: ff1_r = 6'd29;
      32'b????1000000000000000000000000000: ff1_r = 6'd28;
      32'b?????100000000000000000000000000: ff1_r = 6'd27;
      32'b??????10000000000000000000000000: ff1_r = 6'd26;
      32'b???????1000000000000000000000000: ff1_r = 6'd25;
      32'b????????100000000000000000000000: ff1_r = 6'd24;
      32'b?????????10000000000000000000000: ff1_r = 6'd23;
      32'b??????????1000000000000000000000: ff1_r = 6'd22;
      32'b???????????100000000000000000000: ff1_r = 6'd21;
      32'b????????????10000000000000000000: ff1_r = 6'd20;
      32'b?????????????1000000000000000000: ff1_r = 6'd19;
      32'b??????????????100000000000000000: ff1_r = 6'd18;
      32'b???????????????10000000000000000: ff1_r = 6'd17;
      32'b????????????????1000000000000000: ff1_r = 6'd16;
      32'b?????????????????100000000000000: ff1_r = 6'd15;
      32'b??????????????????10000000000000: ff1_r = 6'd14;
      32'b???????????????????1000000000000: ff1_r = 6'd13;
      32'b????????????????????100000000000: ff1_r = 6'd12;
      32'b?????????????????????10000000000: ff1_r = 6'd11;
      32'b??????????????????????1000000000: ff1_r = 6'd10;
      32'b???????????????????????100000000: ff1_r = 6'd9;
      32'b????????????????????????10000000: ff1_r = 6'd8;
      32'b?????????????????????????1000000: ff1_r = 6'd7;
      32'b??????????????????????????100000: ff1_r = 6'd6;
      32'b???????????????????????????10000: ff1_r = 6'd5;
      32'b????????????????????????????1000: ff1_r = 6'd4;
      32'b?????????????????????????????100: ff1_r = 6'd3;
      32'b??????????????????????????????10: ff1_r = 6'd2;
      32'b???????????????????????????????1: ff1_r = 6'd1;
      32'b00000000000000000000000000000000: ff1_r = 6'd0;
    endcase
  end


  //----------------//
  // Barrel shifter //
  //----------------//

  // Bit-reverse on left shift, perform right shift,
  // bit-reverse result on left shift.

  wire op_sll = exec_opc_shift_i[3];
  wire op_srl = exec_opc_shift_i[2];
  wire op_sra = exec_opc_shift_i[1];
  wire op_ror = exec_opc_shift_i[0];

  wire   [EXEDW-1:0] shift_right;
  wire   [EXEDW-1:0] shift_lsw;
  wire   [EXEDW-1:0] shift_msw;
  wire [EXEDW*2-1:0] shift_wide;

  wire   [EXEDW-1:0] shift_result;

  assign shift_lsw =  op_sll ? reverse(exec_1clk_a1_m) : exec_1clk_a1_m;
  assign shift_msw =  op_sra ? {EXEDW{exec_1clk_a1_m[EXEDW-1]}} :
                     (op_ror ? exec_1clk_a1_m : {EXEDW{1'b0}});

  assign shift_wide   = {shift_msw, shift_lsw} >> exec_1clk_b1_m[4:0];
  assign shift_right  = shift_wide[EXEDW-1:0];
  assign shift_result = op_sll ? reverse(shift_right) : shift_right;


  //------------------//
  // Conditional move //
  //------------------//
  wire [EXEDW-1:0] cmov_result;
  assign cmov_result = flag_i ? exec_1clk_a1_m : exec_1clk_b1_m;


  //----------------------------------------//
  // Sign/Zero exentions for 8- and 16-bits //
  //----------------------------------------//
  reg [EXEDW-1:0] extsz_result;
  // ---
  always @(exec_opc_extsz_i or exec_1clk_a1_m) begin
    // synthesis parallel_case
    case (exec_opc_extsz_i)
      {1'b0,`OR1K_ALU_OPC_SECONDARY_EXTBH_EXTBS}:
        extsz_result = {{(EXEDW-8){exec_1clk_a1_m[7]}}, exec_1clk_a1_m[7:0]};
      {1'b0,`OR1K_ALU_OPC_SECONDARY_EXTBH_EXTBZ}:
        extsz_result = {{(EXEDW-8){1'b0}}, exec_1clk_a1_m[7:0]};
      {1'b0,`OR1K_ALU_OPC_SECONDARY_EXTBH_EXTHS}:
        extsz_result = {{(EXEDW-16){exec_1clk_a1_m[15]}}, exec_1clk_a1_m[15:0]};
      {1'b0,`OR1K_ALU_OPC_SECONDARY_EXTBH_EXTHZ}:
        extsz_result = {{(EXEDW-16){1'b0}}, exec_1clk_a1_m[15:0]};
      default:
        extsz_result = exec_1clk_a1_m;
    endcase
  end


  //--------------------//
  // Logical operations //
  //--------------------//
  // Logic result
  reg  [EXEDW-1:0] logic_result;
  // Extract the result, bit-for-bit, from the look-up-table
  integer i;
  always @(exec_lut_logic_i or exec_1clk_a1_m or exec_1clk_b1_m) begin
    for (i = 0; i < EXEDW; i=i+1) begin
      logic_result[i] = exec_lut_logic_i[{exec_1clk_a1_m[i], exec_1clk_b1_m[i]}];
    end
  end


  //------------------------------------------------------------------//
  // Muxing and registering 1-clk results and integer comparison flag //
  //------------------------------------------------------------------//
  wire [EXEDW-1:0] u_1clk_result_mux = ({EXEDW{exec_op_shift_i}} & shift_result   ) |
                                       ({EXEDW{exec_op_ffl1_i}}  & ffl1_result    ) |
                                       ({EXEDW{exec_op_add_i}}   & adder_result   ) |
                                       ({EXEDW{exec_op_logic_i}} & logic_result   ) |
                                       ({EXEDW{exec_op_cmov_i}}  & cmov_result    ) |
                                       ({EXEDW{exec_op_extsz_i}} & extsz_result   ) |
                                       ({EXEDW{exec_op_movhi_i}} & exec_1clk_b1_m );

  //-------------------------------------//
  // update carry flag by 1clk-operation //
  //-------------------------------------//
  wire u_1clk_carry_set      = exec_op_add_i &   adder_u_ovf;
  wire u_1clk_carry_clear    = exec_op_add_i & (~adder_u_ovf);

  //----------------------------------------//
  // update overflow flag by 1clk-operation //
  //----------------------------------------//
  wire u_1clk_overflow_set   = exec_op_add_i &   adder_s_ovf;
  wire u_1clk_overflow_clear = exec_op_add_i & (~adder_s_ovf);


  //--------------------------//
  // Integer comparison logic //
  //--------------------------//
  wire a_eq_b  = (adder_result == {EXEDW{1'b0}}); // Equal compare
  wire a_lts_b = (adder_result_sign ^ adder_s_ovf); // Signed compare (sign != ovf)
  wire a_ltu_b = ~adder_carryout; // Unsigned compare
  // comb.
  reg flag_set;
  always @(exec_opc_setflag_i or a_eq_b or a_lts_b or a_ltu_b) begin
    // synthesis parallel_case
    case(exec_opc_setflag_i)
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
  // ---
  wire u_1clk_flag_set   = exec_op_setflag_i &   flag_set;
  wire u_1clk_flag_clear = exec_op_setflag_i & (~flag_set);


  //-----------------------------------//
  // 1-clock execution write-back miss //
  //-----------------------------------//
  reg             wrbk_1clk_miss_r;
  // ---
  assign taking_1clk_op_o = exec_op_1clk_i & (~wrbk_1clk_miss_r) & // 1CLK TAKING OP
                            ((~exec_flag_carry_req_i) | grant_wrbk_to_1clk_i); // 1CLK TAKING OP
  // ---
  assign op_1clk_valid_o  = exec_op_1clk_i | wrbk_1clk_miss_r;
  // ---
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      wrbk_1clk_miss_r <= 1'b0;
    else if (padv_wrbk_i & grant_wrbk_to_1clk_i)
      wrbk_1clk_miss_r <= 1'b0;
    else if (taking_1clk_op_o)
      wrbk_1clk_miss_r <= 1'b1;
  end //  @clock
  // ---
  reg [EXEDW-1:0] u_1clk_result_p;
  reg             u_1clk_carry_set_p;
  reg             u_1clk_carry_clear_p;
  reg             u_1clk_overflow_set_p;
  reg             u_1clk_overflow_clear_p;
  reg             u_1clk_flag_set_p;
  reg             u_1clk_flag_clear_p;
  // ---
  always @(posedge cpu_clk) begin
    if (taking_1clk_op_o) begin
      u_1clk_result_p         <= u_1clk_result_mux;
      u_1clk_carry_set_p      <= u_1clk_carry_set;
      u_1clk_carry_clear_p    <= u_1clk_carry_clear;
      u_1clk_overflow_set_p   <= u_1clk_overflow_set;
      u_1clk_overflow_clear_p <= u_1clk_overflow_clear;
      u_1clk_flag_set_p       <= u_1clk_flag_set;
      u_1clk_flag_clear_p     <= u_1clk_flag_clear;
    end
  end //  @clock


  // result for in-1clk-unit forwarding
  always @(posedge cpu_clk) begin
    if (taking_1clk_op_o)
      ff_1clk_result_r <= u_1clk_result_mux;
  end //  @clock


  //  registering output for 1-clock operations
  always @(posedge cpu_clk) begin
    if (padv_wrbk_i) begin
      if (grant_wrbk_to_1clk_i)
        wrbk_1clk_result_o <= wrbk_1clk_miss_r ? u_1clk_result_p : u_1clk_result_mux;
      else
        wrbk_1clk_result_o <= {EXEDW{1'b0}};
    end
  end //  @clock

  /****  1CLK Write Back flags ****/
  //  # generate overflow exception by 1clk-operation
  wire   mux_except_overflow_1clk    = except_overflow_enable_i & (wrbk_1clk_miss_r ? u_1clk_overflow_set_p : u_1clk_overflow_set);
  assign exec_except_overflow_1clk_o = grant_wrbk_to_1clk_i & mux_except_overflow_1clk;

  // Write-Back-latchers
  always @(posedge cpu_clk) begin
    if (padv_wrbk_i & grant_wrbk_to_1clk_i) begin
      //  # update carry flag by 1clk-operation
      wrbk_1clk_carry_set_o        <= wrbk_1clk_miss_r ? u_1clk_carry_set_p : u_1clk_carry_set;
      wrbk_1clk_carry_clear_o      <= wrbk_1clk_miss_r ? u_1clk_carry_clear_p : u_1clk_carry_clear;
      //  # update overflow flag by 1clk-operation
      wrbk_1clk_overflow_set_o     <= wrbk_1clk_miss_r ? u_1clk_overflow_set_p : u_1clk_overflow_set;
      wrbk_1clk_overflow_clear_o   <= wrbk_1clk_miss_r ? u_1clk_overflow_clear_p : u_1clk_overflow_clear;
      //  # generate overflow exception by 1clk-operation
      wrbk_except_overflow_1clk_o  <= mux_except_overflow_1clk;
      //  # update SR[F] by 1clk-operation
      wrbk_1clk_flag_set_o         <= wrbk_1clk_miss_r ? u_1clk_flag_set_p : u_1clk_flag_set;
      wrbk_1clk_flag_clear_o       <= wrbk_1clk_miss_r ? u_1clk_flag_clear_p : u_1clk_flag_clear;
    end
    else begin
      //  # update carry flag by 1clk-operation
      wrbk_1clk_carry_set_o        <= 1'b0;
      wrbk_1clk_carry_clear_o      <= 1'b0;
      //  # update overflow flag by 1clk-operation
      wrbk_1clk_overflow_set_o     <= 1'b0;
      wrbk_1clk_overflow_clear_o   <= 1'b0;
      //  # generate overflow exception by 1clk-operation
      wrbk_except_overflow_1clk_o  <= 1'b0;
      //  # update SR[F] by 1clk-operation
      wrbk_1clk_flag_set_o         <= 1'b0;
      wrbk_1clk_flag_clear_o       <= 1'b0;
    end
  end // @clock

endmodule // mor1kx_exec_1clk_marocchino
