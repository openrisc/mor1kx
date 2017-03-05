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
  input                                 padv_wb_i,
  input                                 grant_wb_to_mul_i,

  // input operands from  reservation station
  input      [OPTION_OPERAND_WIDTH-1:0] exec_mul_a1_i,
  input      [OPTION_OPERAND_WIDTH-1:0] exec_mul_b1_i,

  //  other inputs/outputs
  input                                 exec_op_mul_i,
  output                                imul_taking_op_o,
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
  //  ## multiplier stage ready flags
  reg    mul_s1_rdy;
  reg    mul_s2_rdy;
  assign mul_valid_o = mul_s2_rdy; // valid flag is 1-clock ahead of latching for WB
  //  ## stage busy signals
  wire   mul_s2_busy = mul_s2_rdy  & ~(padv_wb_i & grant_wb_to_mul_i);
  wire   mul_s1_busy = mul_s1_rdy  & mul_s2_busy;
  //  ## stage advance signals
  wire   mul_adv_s2  = mul_s1_rdy  & ~mul_s2_busy;
  wire   mul_adv_s1  = exec_op_mul_i & ~mul_s1_busy;

  // integer multiplier is taking operands
  assign imul_taking_op_o = mul_adv_s1;

  // stage #1: register inputs & split them on halfed parts
  reg [MULHDW-1:0] mul_s1_al;
  reg [MULHDW-1:0] mul_s1_bl;
  reg [MULHDW-1:0] mul_s1_ah;
  reg [MULHDW-1:0] mul_s1_bh;
  //  registering
  always @(posedge clk) begin
    if (mul_adv_s1) begin
      mul_s1_al <= exec_mul_a1_i[MULHDW-1:0];
      mul_s1_bl <= exec_mul_b1_i[MULHDW-1:0];
      mul_s1_ah <= exec_mul_a1_i[MULDW-1:MULHDW];
      mul_s1_bh <= exec_mul_b1_i[MULDW-1:MULHDW];
    end
  end // @clock
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
  end // @clock

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
  end // @clock
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
  end // @clock

  // stage #3: result
  wire [MULDW-1:0] mul_s3t_sum;
  assign mul_s3t_sum = {mul_s2_bhal[MULHDW-1:0],{MULHDW{1'b0}}} +
                       {mul_s2_ahbl[MULHDW-1:0],{MULHDW{1'b0}}} +
                        mul_s2_albl;
  //  registering
  always @(posedge clk) begin
    if (padv_wb_i)
      wb_mul_result_o <= {MULDW{grant_wb_to_mul_i}} & mul_s3t_sum;
  end // @clock

endmodule // mor1kx_multiplier_marocchino


//----------------------------------------------------------------------------//
// SRT-4 kernel                                                               //
//   Denominator is normalized: [0.5 ... 1)                                   //
//   Both are unsigned                                                        //
//   Numerator is left shifted by number of positions were used for           //
// denominator normalization, so it's MSB value is always 0                   //
//   Numerator and Denominator formats are (being written as fractionals):    //
// num [2n-1:0] = "0." 0 num(2n-2) ... num(n-1) ... num(0)                    //
// den  [n-1:0] = "0." 1 den(n-2)  ... den(0)                                 //
//   Conditions:                                                              //
// (a) -den <= num < den                                                      //
// (b) "n" : must be even                                                     //
//   Quotient is in 2's complement form:                                      //
// qtnt [n-1:0] =  qtnt(n-1) ... qtnt(0)                                      //
//   Reminder is not returned                                                 //
//----------------------------------------------------------------------------//

module srt4_kernel
#(
    parameter N      = 16, // must be even
    parameter LOG2N2 =  3  // ceil(log2(N/2)): size of iteration counter
)
(
  // clock and reset
  input              clk,
  input              rst,
  // pipeline controls
  input              pipeline_flush_i,
  input              div_start_i,      // take operands and start
  output reg         div_proc_o,       // iterator busy
  output reg         div_valid_o,      // result ready
  input              wb_taking_div_i,  // Write Back is taking result
  // numerator and denominator
  input    [2*N-1:0] num_i,
  input      [N-1:0] den_i,
  // signum for output
  input              div_neg_i,        // result should be negative
  // outputs
  output reg         dbz_o,
  //output     [N-1:0] rem_o,
  output     [N-1:0] qtnt_o
);

  // Reminder
  wire   [N:0] four_rem;   // 4*rem
  wire   [N:0] nrem;       // next reminder (4*rem - q_digit*den)
  reg    [N:0] prem_hi_r;  // partial reminder: initially = {0,num(2n-1)...num(n)}
  reg  [N-1:0] prem_lo_r;  // partial reminder: initially = {num(n-1)...num(0)}
  wire   [3:0] trunc_rem;  // truncated partial reminder


  // Each iteration starts from qoutient digit selection
  assign trunc_rem = prem_hi_r[N:N-3];
  // quotient's special digits
  reg [2:0] q_digit_2or3_r;
  reg [2:0] q_digit_minus_2or3_r;
  // ---
  always @(posedge clk) begin
    if (div_start_i) begin
      q_digit_2or3_r       <= {2'b01, ~den_i[N-2]};
      q_digit_minus_2or3_r <= { 1'b1,  den_i[N-2], ~den_i[N-2]};
    end
  end
  // signed digit selection
  reg [2:0] q_digit; // [2] - signum
  // ---
  always @(*) begin
    // synthesis parallel_case full_case
    casez (trunc_rem)
      4'b0000: q_digit = 3'b000;
      4'b0001: q_digit = 3'b001;
      4'b0010: q_digit = 3'b010;
      4'b0011: q_digit = q_digit_2or3_r;
      4'b01??: q_digit = 3'b011; // 0100 ... 0111
      4'b10??: q_digit = 3'b101; // 1000 ... 1011
      4'b1100: q_digit = q_digit_minus_2or3_r;
      4'b1101: q_digit = 3'b110;
      4'b1110: q_digit = 3'b111;
      default: q_digit = 3'b000;
    endcase
  end

  // Prepare multiple versions of denominator
  reg [N-1:0] one_den_r;    // 1 * denominator
  reg   [N:0] three_den_r;  // 3 * denominator
  // ---
  always @(posedge clk) begin
    if (div_start_i) begin
      one_den_r   <= den_i;
      three_den_r <= {1'b0, den_i} + {den_i, 1'b0};
    end
  end
  // select the multiple denominator
  reg [N:0] mult_den; // : 0 / den / 2*den / 3*den
  // second operand selection
  always @(*) begin
    // synthesis parallel_case full_case
    case (q_digit)
      3'b000:  mult_den = {(N+1){1'b0}};     // 0 * denominator
      3'b001:  mult_den = {1'b0, one_den_r}; // 1 * denominator
      3'b010:  mult_den = {one_den_r, 1'b0}; // 2 * denominator
      3'b011:  mult_den = three_den_r;       // 3 * denominator
      3'b101:  mult_den = three_den_r;       // 3 * denominator
      3'b110:  mult_den = {one_den_r, 1'b0}; // 2 * denominator
      default: mult_den = {1'b0, one_den_r}; // 1 * denominator
    endcase
  end

  assign four_rem  = {prem_hi_r[N-2:0],prem_lo_r[N-1:N-2]};
  // next reminder
  wire   sub  = ~q_digit[2]; // substract
  // sub ? (4*REM - MultDen) : (4*REM + MultDen)
  assign nrem = four_rem + (mult_den ^ {(N+1){sub}}) + {{N{1'b0}},sub};

  // and partial reminder update
  always @(posedge clk) begin
    if (div_start_i) begin
      prem_hi_r <= {1'b0,num_i[2*N-1:N]};
      prem_lo_r <= num_i[N-1:0];
    end
    else if (div_proc_o) begin
      prem_hi_r <= nrem;
      prem_lo_r <= {prem_lo_r[N-3:0],2'b00};
    end
  end // @clock

  // signed digits to tow's complement on the fly convertor
  //  # part Q
  reg   [N-1:0] q_r;
  //  # ---
  always @(posedge clk) begin
    if (div_start_i)
      q_r <= {N{1'b0}};
    else if (div_proc_o) begin
      // synthesis parallel_case full_case
      case (q_digit)
        3'b000:  q_r <= { q_r[N-3:0],2'b00};
        3'b001:  q_r <= { q_r[N-3:0],2'b01};
        3'b010:  q_r <= { q_r[N-3:0],2'b10};
        3'b011:  q_r <= { q_r[N-3:0],2'b11};
        3'b101:  q_r <= {qm_r[N-3:0],2'b01};
        3'b110:  q_r <= {qm_r[N-3:0],2'b10};
        default: q_r <= {qm_r[N-3:0],2'b11};
      endcase
    end
  end // @clock
  //  # part QM
  reg   [N-1:0] qm_r;
  //  # ---
  always @(posedge clk) begin
    if (div_start_i)
      qm_r <= {{(N-2){1'b0}},2'b11};
    else if (div_proc_o) begin
      // synthesis parallel_case full_case
      case (q_digit)
        3'b000:  qm_r <= {qm_r[N-3:0],2'b11};
        3'b001:  qm_r <= { q_r[N-3:0],2'b00};
        3'b010:  qm_r <= { q_r[N-3:0],2'b01};
        3'b011:  qm_r <= { q_r[N-3:0],2'b10};
        3'b101:  qm_r <= {qm_r[N-3:0],2'b00};
        3'b110:  qm_r <= {qm_r[N-3:0],2'b01};
        default: qm_r <= {qm_r[N-3:0],2'b10};
      endcase
    end
  end // @clock

  // Outputs
  //  # if REM < 0 than { REM += D; Q -= 1; }
  //  # reminder
  //assign rem_o  = prem_hi_r[N-1:0] + ({N{prem_hi_r[N]}} & one_den_r[N-1:0]);
  //  # quotient
  reg div_neg_r; // negate result
  always @(posedge clk) begin
    if (div_start_i) begin
      div_neg_r <= div_neg_i;
    end
  end
  // ---
  assign qtnt_o = ((q_r + {N{prem_hi_r[N]}}) ^ {N{div_neg_r}}) + {{(N-1){1'b0}},div_neg_r};


  // iterations controller
  wire dbz = ~(|den_i); // division by zero
  // ---
  localparam [LOG2N2-1:0] DIV_COUNT_MAX = ((N / 2) - 1);
  // ---
  reg [LOG2N2-1:0] div_count_r;
  // division controller
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      div_valid_o <= 1'b0;
      dbz_o       <= 1'b0;
      div_proc_o  <= 1'b0;
      div_count_r <= {LOG2N2{1'b0}};
    end
    else if (pipeline_flush_i) begin
      div_valid_o <= 1'b0;
      dbz_o       <= 1'b0;
      div_proc_o  <= 1'b0;
      div_count_r <= {LOG2N2{1'b0}};
    end
    else if (div_start_i) begin
      if (dbz) begin
        div_valid_o <= 1'b1;
        dbz_o       <= 1'b1;
        div_proc_o  <= 1'b0;
        div_count_r <= {LOG2N2{1'b0}};
      end
      else begin
        div_valid_o <= 1'b0;
        dbz_o       <= 1'b0;
        div_proc_o  <= 1'b1;
        div_count_r <= DIV_COUNT_MAX;
      end
    end
    else if (wb_taking_div_i) begin
      div_valid_o <= 1'b0;
      dbz_o       <= 1'b0;
      div_proc_o  <= 1'b0;
      div_count_r <= {LOG2N2{1'b0}};
    end
    else if (div_proc_o) begin
      if (~(|div_count_r)) begin // == 0
        div_valid_o <= 1'b1;
        div_proc_o  <= 1'b0;
      end
      else
        div_count_r <= div_count_r + {LOG2N2{1'b1}}; // -= 1
    end
  end // @clock

endmodule // srt4_kernel


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
  input                                 padv_wb_i,
  input                                 grant_wb_to_div_i,

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
  output reg                            wb_div_carry_set_o,
  output reg                            wb_div_carry_clear_o,
  //  # update overflow flag by division
  output reg                            wb_div_overflow_set_o,
  output reg                            wb_div_overflow_clear_o,
  //  # generate overflow exception by division
  input                                 except_overflow_enable_i,
  output                                exec_except_overflow_div_o,
  output reg                            wb_except_overflow_div_o,
  //  # division result
  output reg [OPTION_OPERAND_WIDTH-1:0] wb_div_result_o
);

 `ifndef SYNTHESIS // DIV: Normalization supports 32-bits operands only
  // synthesis translate_off
  generate
  if (OPTION_OPERAND_WIDTH != 32) begin
    initial begin
      $display("INT DIV ERROR: Normalization supports 32-bits operands only");
      $finish();
    end
  end
  endgenerate
  // synthesis translate_on
 `endif // !synth

  localparam DIVDW        = OPTION_OPERAND_WIDTH; // short name
  localparam LOG2_DIVDW_2 = 4; // ceil(log2(DIVDW/2)): size of iteration counter

  // divider controls
  //  ## Write Back taking DIV result
  wire wb_taking_div = padv_wb_i & grant_wb_to_div_i;
  //  ## per stage ready flags
  reg  div_s1_rdy;
  reg  div_s2_rdy;
  //  ## stage busy signals
  wire div_proc; // SRT-4 kernel is busy
  wire div_s3_busy = div_proc | (div_valid_o & ~wb_taking_div);
  wire div_s2_busy = div_s2_rdy  & div_s3_busy;
  wire div_s1_busy = div_s1_rdy  & div_s2_busy;
  //  ## stage advance signals
  wire div_adv_s3  = div_s2_rdy  & ~div_s3_busy;
  wire div_adv_s2  = div_s1_rdy  & ~div_s2_busy;
  wire div_adv_s1  = exec_op_div_i & ~div_s1_busy;

  //  # integer divider is taking operands
  assign idiv_taking_op_o = div_adv_s1;

  /**** DIV Stage 1 ****/
  // Absolute values computation
  // Convert negative operands in the case of signed division.
  // If only one of the operands is negative, the result is
  // converted back to negative later on
  //  # signums
  wire s1t_div_sign_a = exec_div_a1_i[DIVDW-1] & exec_op_div_signed_i;
  wire s1t_div_sign_b = exec_div_b1_i[DIVDW-1] & exec_op_div_signed_i;
  //  # modulos
  wire [DIVDW-1:0] s1t_div_a = (exec_div_a1_i ^ {DIVDW{s1t_div_sign_a}}) + {{(DIVDW-1){1'b0}},s1t_div_sign_a};
  wire [DIVDW-1:0] s1t_div_b = (exec_div_b1_i ^ {DIVDW{s1t_div_sign_b}}) + {{(DIVDW-1){1'b0}},s1t_div_sign_b};
  //  # nlz of denominator
  reg [4:0] s1t_div_b_nlz;
  // ---
  always @(s1t_div_b) begin
    // synthesis parallel_case full_case
    casez (s1t_div_b)
      32'b1???????????????????????????????: s1t_div_b_nlz =  5'd0;
      32'b01??????????????????????????????: s1t_div_b_nlz =  5'd1;
      32'b001?????????????????????????????: s1t_div_b_nlz =  5'd2;
      32'b0001????????????????????????????: s1t_div_b_nlz =  5'd3;
      32'b00001???????????????????????????: s1t_div_b_nlz =  5'd4;
      32'b000001??????????????????????????: s1t_div_b_nlz =  5'd5;
      32'b0000001?????????????????????????: s1t_div_b_nlz =  5'd6;
      32'b00000001????????????????????????: s1t_div_b_nlz =  5'd7;
      32'b000000001???????????????????????: s1t_div_b_nlz =  5'd8;
      32'b0000000001??????????????????????: s1t_div_b_nlz =  5'd9;
      32'b00000000001?????????????????????: s1t_div_b_nlz = 5'd10;
      32'b000000000001????????????????????: s1t_div_b_nlz = 5'd11;
      32'b0000000000001???????????????????: s1t_div_b_nlz = 5'd12;
      32'b00000000000001??????????????????: s1t_div_b_nlz = 5'd13;
      32'b000000000000001?????????????????: s1t_div_b_nlz = 5'd14;
      32'b0000000000000001????????????????: s1t_div_b_nlz = 5'd15;
      32'b00000000000000001???????????????: s1t_div_b_nlz = 5'd16;
      32'b000000000000000001??????????????: s1t_div_b_nlz = 5'd17;
      32'b0000000000000000001?????????????: s1t_div_b_nlz = 5'd18;
      32'b00000000000000000001????????????: s1t_div_b_nlz = 5'd19;
      32'b000000000000000000001???????????: s1t_div_b_nlz = 5'd20;
      32'b0000000000000000000001??????????: s1t_div_b_nlz = 5'd21;
      32'b00000000000000000000001?????????: s1t_div_b_nlz = 5'd22;
      32'b000000000000000000000001????????: s1t_div_b_nlz = 5'd23;
      32'b0000000000000000000000001???????: s1t_div_b_nlz = 5'd24;
      32'b00000000000000000000000001??????: s1t_div_b_nlz = 5'd25;
      32'b000000000000000000000000001?????: s1t_div_b_nlz = 5'd26;
      32'b0000000000000000000000000001????: s1t_div_b_nlz = 5'd27;
      32'b00000000000000000000000000001???: s1t_div_b_nlz = 5'd28;
      32'b000000000000000000000000000001??: s1t_div_b_nlz = 5'd29;
      32'b0000000000000000000000000000001?: s1t_div_b_nlz = 5'd30;
      32'b00000000000000000000000000000001: s1t_div_b_nlz = 5'd31;
      32'b00000000000000000000000000000000: s1t_div_b_nlz =  5'd0;
    endcase
  end // always
  // ---
  reg             s1o_div_signed, s1o_div_unsigned,
                  s1o_div_neg;
  reg [DIVDW-1:0] s1o_div_a;
  reg [DIVDW-1:0] s1o_div_b;
  reg       [4:0] s1o_div_b_nlz;
  // ---
  always @(posedge clk) begin
    if (div_adv_s1) begin
      s1o_div_a        <= s1t_div_a;
      s1o_div_b        <= s1t_div_b;
      s1o_div_b_nlz    <= s1t_div_b_nlz;
      s1o_div_neg      <= (s1t_div_sign_a ^ s1t_div_sign_b);
      s1o_div_signed   <= exec_op_div_signed_i;
      s1o_div_unsigned <= exec_op_div_unsigned_i;
    end
  end // @clock
  //  ready flag
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      div_s1_rdy <= 1'b0;
    else if (pipeline_flush_i)
      div_s1_rdy <= 1'b0;
    else if (div_adv_s1)
      div_s1_rdy <= 1'b1;
    else if (div_adv_s2)
      div_s1_rdy <= 1'b0;
  end // @clock


  /**** DIV Stage 2 ****/
  // Normalization
  wire [2*DIVDW-1:0] s2t_div_a = s1o_div_a << s1o_div_b_nlz;
  wire   [DIVDW-1:0] s2t_div_b = s1o_div_b << s1o_div_b_nlz;
  // ---
  reg               s2o_div_signed, s2o_div_unsigned,
                    s2o_div_neg;
  reg [2*DIVDW-1:0] s2o_div_a;
  reg   [DIVDW-1:0] s2o_div_b;
  // ---
  always @(posedge clk) begin
    if (div_adv_s2) begin
      s2o_div_a        <= s2t_div_a;
      s2o_div_b        <= s2t_div_b;
      s2o_div_neg      <= s1o_div_neg;
      s2o_div_signed   <= s1o_div_signed;
      s2o_div_unsigned <= s1o_div_unsigned;
    end
  end // @clock
  //  ready flag
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      div_s2_rdy <= 1'b0;
    else if (pipeline_flush_i)
      div_s2_rdy <= 1'b0;
    else if (div_adv_s2)
      div_s2_rdy <= 1'b1;
    else if (div_adv_s3)
      div_s2_rdy <= 1'b0;
  end // @clock


  /**** DIV Stage 3 ****/
  // Compute denominator multiplies and run iterations
  wire [DIVDW-1:0] s3t_div_result;
  wire             s3o_dbz;
  reg              s3o_div_signed, s3o_div_unsigned;
  // ---
  always @(posedge clk) begin
    if (div_adv_s3) begin
      s3o_div_signed   <= s2o_div_signed;
      s3o_div_unsigned <= s2o_div_unsigned;
    end
  end // @clock
  // ---
  srt4_kernel
  #(
     .N       (DIVDW), // SRT_4_KERNEL
     .LOG2N2  (LOG2_DIVDW_2) // SRT_4_KERNEL
  )
  u_srt4_kernel
  (
    // clock and reset
    .clk                (clk), // SRT_4_KERNEL
    .rst                (rst), // SRT_4_KERNEL
    // pipeline controls
    .pipeline_flush_i   (pipeline_flush_i), // SRT_4_KERNEL
    .div_start_i        (div_adv_s3), // SRT_4_KERNEL
    .div_proc_o         (div_proc), // SRT_4_KERNEL
    .div_valid_o        (div_valid_o), // SRT_4_KERNEL
    .wb_taking_div_i    (wb_taking_div), // SRT_4_KERNEL
    // numerator and denominator
    .num_i              (s2o_div_a), // SRT_4_KERNEL
    .den_i              (s2o_div_b), // SRT_4_KERNEL
    // signum for output
    .div_neg_i          (s2o_div_neg), // SRT_4_KERNEL
    // outputs
    .dbz_o              (s3o_dbz), // SRT_4_KERNEL
    //.rem_o              (remainder),
    .qtnt_o             (s3t_div_result) // SRT_4_KERNEL
  );

  /**** DIV Write Back result ****/

  always @(posedge clk) begin
    if (padv_wb_i)
      wb_div_result_o <= {DIVDW{grant_wb_to_div_i}} & s3t_div_result;
  end //  @clock

  /****  DIV Write Back flags ****/

  //  # update carry flag by division
  wire exec_div_carry_set      = grant_wb_to_div_i & s3o_div_unsigned &   s3o_dbz;
  wire exec_div_carry_clear    = grant_wb_to_div_i & s3o_div_unsigned & (~s3o_dbz);

  //  # update overflow flag by division
  wire exec_div_overflow_set   = grant_wb_to_div_i & s3o_div_signed &   s3o_dbz;
  wire exec_div_overflow_clear = grant_wb_to_div_i & s3o_div_signed & (~s3o_dbz);

  //  # generate overflow exception by division
  assign exec_except_overflow_div_o = except_overflow_enable_i & exec_div_overflow_set;

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
      wb_except_overflow_div_o  <= exec_except_overflow_div_o;
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
  input                                 clk,
  input                                 rst,

  // pipeline control signal in
  input                                 pipeline_flush_i,
  input                                 padv_wb_i,
  input                                 grant_wb_to_1clk_i,

  // input operands A and B with forwarding from WB
  input      [OPTION_OPERAND_WIDTH-1:0] exec_1clk_a1_i,
  input      [OPTION_OPERAND_WIDTH-1:0] exec_1clk_b1_i,

  // 1-clock instruction auxiliaries
  input       [`OR1K_ALU_OPC_WIDTH-1:0] exec_opc_alu_secondary_i,
  input                                 carry_i, // feedback from ctrl
  input                                 flag_i, // feedback from ctrl (for cmov)

  // adder's inputs
  input                                 exec_op_add_i,
  input                                 exec_adder_do_sub_i,
  input                                 exec_adder_do_carry_i,
  // shift, ffl1, movhi, cmov
  input                                 exec_op_shift_i,
  input                                 exec_op_ffl1_i,
  input                                 exec_op_movhi_i,
  input                                 exec_op_cmov_i,
  // logic
  input                                 exec_op_logic_i,
  input       [`OR1K_ALU_OPC_WIDTH-1:0] exec_opc_logic_i,
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
  output                                exec_except_overflow_1clk_o,
  output reg                            wb_except_overflow_1clk_o,

  // integer comparison flag
  input                                 exec_op_setflag_i,
  // WB: integer comparison result
  output reg                            wb_int_flag_set_o,
  output reg                            wb_int_flag_clear_o,

  // FP32 comparison flag
  input                                 exec_op_fp32_cmp_i,
  input                           [2:0] exec_opc_fp32_cmp_i,
  input                                 except_fpu_enable_i,
  input                                 ctrl_fpu_mask_flags_inv_i,
  input                                 ctrl_fpu_mask_flags_inf_i,
  // EXEC: not latched pre-WB
  output                                exec_except_fp32_cmp_o,
  // WB: FP32 comparison results
  output                                wb_fp32_flag_set_o,
  output                                wb_fp32_flag_clear_o,
  output                                wb_fp32_cmp_inv_o,
  output                                wb_fp32_cmp_inf_o,
  output                                wb_fp32_cmp_wb_fpcsr_o,
  output                                wb_except_fp32_cmp_o,

  // Forwarding comparision flag result for conditional branch take/not
  output                                exec_flag_set_o    // integer or fp32 comparison result
);

  localparam  EXEDW = OPTION_OPERAND_WIDTH; // short name


  //------------------//
  // Adder/subtractor //
  //------------------//
  // outputs
  wire             adder_carryout;
  wire [EXEDW-1:0] adder_result;
  // inputs
  wire [EXEDW-1:0] b_mux = {EXEDW{exec_adder_do_sub_i}} ^ exec_1clk_b1_i; // inverse for l.sub
  wire carry_in = exec_adder_do_sub_i | (exec_adder_do_carry_i & carry_i);
  // Adder
  assign {adder_carryout, adder_result} =
           exec_1clk_a1_i + b_mux + {{(EXEDW-1){1'b0}},carry_in};
  // result sign
  wire adder_result_sign = adder_result[EXEDW-1];
  // signed overflow detection
  // Input signs are same and result sign is different to input signs
  wire adder_s_ovf =
         (exec_1clk_a1_i[EXEDW-1] == b_mux[EXEDW-1]) &
         (exec_1clk_a1_i[EXEDW-1] ^ adder_result[EXEDW-1]);
  // unsigned overflow detection
  wire adder_u_ovf = adder_carryout;


  //------//
  // FFL1 //
  //------//
  wire [EXEDW-1:0] ffl1_result;
  assign ffl1_result = (exec_opc_alu_secondary_i[2]) ?
           (exec_1clk_a1_i[31] ? 32 : exec_1clk_a1_i[30] ? 31 : exec_1clk_a1_i[29] ? 30 :
            exec_1clk_a1_i[28] ? 29 : exec_1clk_a1_i[27] ? 28 : exec_1clk_a1_i[26] ? 27 :
            exec_1clk_a1_i[25] ? 26 : exec_1clk_a1_i[24] ? 25 : exec_1clk_a1_i[23] ? 24 :
            exec_1clk_a1_i[22] ? 23 : exec_1clk_a1_i[21] ? 22 : exec_1clk_a1_i[20] ? 21 :
            exec_1clk_a1_i[19] ? 20 : exec_1clk_a1_i[18] ? 19 : exec_1clk_a1_i[17] ? 18 :
            exec_1clk_a1_i[16] ? 17 : exec_1clk_a1_i[15] ? 16 : exec_1clk_a1_i[14] ? 15 :
            exec_1clk_a1_i[13] ? 14 : exec_1clk_a1_i[12] ? 13 : exec_1clk_a1_i[11] ? 12 :
            exec_1clk_a1_i[10] ? 11 : exec_1clk_a1_i[9] ? 10 : exec_1clk_a1_i[8] ? 9 :
            exec_1clk_a1_i[7] ? 8 : exec_1clk_a1_i[6] ? 7 : exec_1clk_a1_i[5] ? 6 : exec_1clk_a1_i[4] ? 5 :
            exec_1clk_a1_i[3] ? 4 : exec_1clk_a1_i[2] ? 3 : exec_1clk_a1_i[1] ? 2 : exec_1clk_a1_i[0] ? 1 : 0 ) :
           (exec_1clk_a1_i[0] ? 1 : exec_1clk_a1_i[1] ? 2 : exec_1clk_a1_i[2] ? 3 : exec_1clk_a1_i[3] ? 4 :
            exec_1clk_a1_i[4] ? 5 : exec_1clk_a1_i[5] ? 6 : exec_1clk_a1_i[6] ? 7 : exec_1clk_a1_i[7] ? 8 :
            exec_1clk_a1_i[8] ? 9 : exec_1clk_a1_i[9] ? 10 : exec_1clk_a1_i[10] ? 11 : exec_1clk_a1_i[11] ? 12 :
            exec_1clk_a1_i[12] ? 13 : exec_1clk_a1_i[13] ? 14 : exec_1clk_a1_i[14] ? 15 :
            exec_1clk_a1_i[15] ? 16 : exec_1clk_a1_i[16] ? 17 : exec_1clk_a1_i[17] ? 18 :
            exec_1clk_a1_i[18] ? 19 : exec_1clk_a1_i[19] ? 20 : exec_1clk_a1_i[20] ? 21 :
            exec_1clk_a1_i[21] ? 22 : exec_1clk_a1_i[22] ? 23 : exec_1clk_a1_i[23] ? 24 :
            exec_1clk_a1_i[24] ? 25 : exec_1clk_a1_i[25] ? 26 : exec_1clk_a1_i[26] ? 27 :
            exec_1clk_a1_i[27] ? 28 : exec_1clk_a1_i[28] ? 29 : exec_1clk_a1_i[29] ? 30 :
            exec_1clk_a1_i[30] ? 31 : exec_1clk_a1_i[31] ? 32 : 0);


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

  wire op_sll = (exec_opc_alu_secondary_i == `OR1K_ALU_OPC_SECONDARY_SHRT_SLL);
  wire op_srl = (exec_opc_alu_secondary_i == `OR1K_ALU_OPC_SECONDARY_SHRT_SRL);
  wire op_sra = (exec_opc_alu_secondary_i == `OR1K_ALU_OPC_SECONDARY_SHRT_SRA);
  wire op_ror = (exec_opc_alu_secondary_i == `OR1K_ALU_OPC_SECONDARY_SHRT_ROR);

  wire [EXEDW-1:0] shift_right;
  wire [EXEDW-1:0] shift_lsw;
  wire [EXEDW-1:0] shift_msw;

  wire [EXEDW-1:0] shift_result;

  assign shift_lsw = op_sll ? reverse(exec_1clk_a1_i) : exec_1clk_a1_i;
  assign shift_msw = op_sra ? {EXEDW{exec_1clk_a1_i[EXEDW-1]}} :
                     op_ror ? exec_1clk_a1_i : {EXEDW{1'b0}};

  assign shift_right = {shift_msw, shift_lsw} >> exec_1clk_b1_i[4:0];
  assign shift_result = op_sll ? reverse(shift_right) : shift_right;


  //------------------//
  // Conditional move //
  //------------------//
  wire [EXEDW-1:0] cmov_result;
  assign cmov_result = flag_i ? exec_1clk_a1_i : exec_1clk_b1_i;


  //--------------------//
  // Logical operations //
  //--------------------//
  // Logic wires
  reg [EXEDW-1:0]  logic_result;
  // Create a look-up-table for AND/OR/XOR
  reg [3:0] logic_lut;
  always @(*) begin
    // synthesis parallel_case full_case
    case(exec_opc_logic_i)
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
      logic_result[i] = logic_lut[{exec_1clk_a1_i[i], exec_1clk_b1_i[i]}];
    end
  end


  //------------------------------------------------------------------//
  // Muxing and registering 1-clk results and integer comparison flag //
  //------------------------------------------------------------------//
  wire [EXEDW-1:0] alu_1clk_result_mux = ({EXEDW{exec_op_shift_i}} & shift_result   ) |
                                         ({EXEDW{exec_op_ffl1_i}}  & ffl1_result    ) |
                                         ({EXEDW{exec_op_add_i}}   & adder_result   ) |
                                         ({EXEDW{exec_op_logic_i}} & logic_result   ) |
                                         ({EXEDW{exec_op_cmov_i}}  & cmov_result    ) |
                                         ({EXEDW{exec_op_movhi_i}} & exec_1clk_b1_i );

  //  registering output for 1-clock operations
  always @(posedge clk) begin
    if (padv_wb_i)
      wb_alu_1clk_result_o <= {EXEDW{grant_wb_to_1clk_i}} & alu_1clk_result_mux;
  end //  @clock

  /****  1CLK Write Back flags ****/

  //  # update carry flag by 1clk-operation
  wire exec_1clk_carry_set      = grant_wb_to_1clk_i & exec_op_add_i &   adder_u_ovf;
  wire exec_1clk_carry_clear    = grant_wb_to_1clk_i & exec_op_add_i & (~adder_u_ovf);

  //  # update overflow flag by 1clk-operation
  wire exec_1clk_overflow_set   = grant_wb_to_1clk_i & exec_op_add_i &   adder_s_ovf;
  wire exec_1clk_overflow_clear = grant_wb_to_1clk_i & exec_op_add_i & (~adder_s_ovf);

  //  # generate overflow exception by 1clk-operation
  assign exec_except_overflow_1clk_o = except_overflow_enable_i & exec_1clk_overflow_set;

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
      wb_except_overflow_1clk_o  <= exec_except_overflow_1clk_o;
    end
  end // @clock


  //--------------------------//
  // Integer comparison logic //
  //--------------------------//
  wire a_eq_b  = (exec_1clk_a1_i == exec_1clk_b1_i); // Equal compare
  wire a_lts_b = (adder_result_sign ^ adder_s_ovf); // Signed compare (sign != ovf)
  wire a_ltu_b = ~adder_carryout; // Unsigned compare
  // comb.
  reg flag_set;
  always @* begin
    // synthesis parallel_case full_case
    case(exec_opc_alu_secondary_i)
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
      wb_int_flag_set_o   <= exec_op_setflag_i & grant_wb_to_1clk_i &   flag_set;
      wb_int_flag_clear_o <= exec_op_setflag_i & grant_wb_to_1clk_i & (~flag_set);
    end // wb advance
  end // @clock


  //------------------------//
  // FP-32 comparison logic //
  //------------------------//
  wire fp32_flag_set; // for forwarding to branch prediction
  // ---
  pfpu32_fcmp_marocchino u_f32_cmp
  (
    // clock and reset
    .clk                    (clk), // fp32-cmp
    .rst                    (rst),
    // pipeline controls
    .pipeline_flush_i       (pipeline_flush_i),   // fp32-cmp.flush pipe
    .padv_wb_i              (padv_wb_i),          // fp32-cmp. advance output latches
    .grant_wb_to_1clk_i     (grant_wb_to_1clk_i), // fp32-cmp
    // command
    .op_fp32_cmp_i          (exec_op_fp32_cmp_i), // fp32-cmp
    .opc_fp32_cmp_i         (exec_opc_fp32_cmp_i), // fp32-cmp
    // Operands
    .rfa_i                  (exec_1clk_a1_i), // fp32-cmp
    .rfb_i                  (exec_1clk_b1_i), // fp32-cmp
    // Modes
    .except_fpu_enable_i        (except_fpu_enable_i), // fp32-cmp
    .ctrl_fpu_mask_flags_inv_i  (ctrl_fpu_mask_flags_inv_i), // fp32-cmp
    .ctrl_fpu_mask_flags_inf_i  (ctrl_fpu_mask_flags_inf_i), // fp32-cmp
    // Outputs
    //  # not WB-latched for flag forwarding
    .fp32_flag_set_o        (fp32_flag_set),
    //  # not latched pre-WB
    .exec_except_fp32_cmp_o (exec_except_fp32_cmp_o), // fp32-cmp
    //  # WB-latched
    .wb_fp32_flag_set_o     (wb_fp32_flag_set_o),   // fp32-cmp  result
    .wb_fp32_flag_clear_o   (wb_fp32_flag_clear_o), // fp32-cmp  result
    .wb_fp32_cmp_inv_o      (wb_fp32_cmp_inv_o), // fp32-cmp flag 'invalid'
    .wb_fp32_cmp_inf_o      (wb_fp32_cmp_inf_o), // fp32-cmp flag 'infinity'
    .wb_fp32_cmp_wb_fpcsr_o (wb_fp32_cmp_wb_fpcsr_o), // fp32-cmp update FPCSR
    .wb_except_fp32_cmp_o   (wb_except_fp32_cmp_o) // fp32-cmp exception
  );


  //--------------------------------------------------------------------//
  // Forwarding comparision flag result for conditional branch take/not //
  //--------------------------------------------------------------------//
  assign exec_flag_set_o = (exec_op_setflag_i & flag_set) | (exec_op_fp32_cmp_i & fp32_flag_set);

endmodule // mor1kx_exec_1clk_marocchino
