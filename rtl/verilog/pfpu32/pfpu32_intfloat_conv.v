/////////////////////////////////////////////////////////////////////
////                                                             ////
////  pfpu32_intfloat_conv                                       ////
////  Pipelined conversion between 32-bit integer and single     ////
////  precision floating point format                            ////
////                                                             ////
////  Author: Rudolf Usselmann                                   ////
////          rudi@asics.ws                                      ////
////                                                             ////
////  Modified by Julius Baxter, July, 2010                      ////
////              julius.baxter@orsoc.se                         ////
////                                                             ////
////  Update for mor1kx, bug fixing and further development      ////
////              Andrey Bacherov, 2014,                         ////
////              avbacherov@opencores.org                       ////
////                                                             ////
/////////////////////////////////////////////////////////////////////
////                                                             ////
//// Copyright (C) 2000 Rudolf Usselmann                         ////
////                    rudi@asics.ws                            ////
////                                                             ////
//// This source file may be used and distributed without        ////
//// restriction provided that this copyright statement is not   ////
//// removed from the file and that any derivative work contains ////
//// the original copyright notice and the associated disclaimer.////
////                                                             ////
////     THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY     ////
//// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED   ////
//// TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS   ////
//// FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL THE AUTHOR      ////
//// OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,         ////
//// INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES    ////
//// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE   ////
//// GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR        ////
//// BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF  ////
//// LIABILITY, WHETHER IN  CONTRACT, STRICT LIABILITY, OR TORT  ////
//// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT  ////
//// OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE         ////
//// POSSIBILITY OF SUCH DAMAGE.                                 ////
////                                                             ////
/////////////////////////////////////////////////////////////////////

`include "mor1kx-defines.v"

/*

 FPU Operations (fpu_op):
 ========================

 0 =
 1 =
 2 =
 3 =
 4 = int to float
 5 = float to int
 6 =
 7 =

 Rounding Modes (rmode):
 =======================

 0 = round_nearest_even
 1 = round_to_zero
 2 = round_up
 3 = round_down

 */


module pfpu32_intfloat_conv
(
   input             clk,
   input             rst,
   input [1:0]       rmode_i,
   input [2:0]       fpu_op_i, // 4: i2f, 5: f2i
   input [31:0]      opa_i,
   input             flush_i,  // flushe pipe
   input             adv_i,    // advance pipe
   input             start_i,  // start conversion
   output reg [31:0] out_o,
   output reg        snan_o,
   output reg        ine_o,
   output reg        inv_o,
   output reg        underflow_o,
   output reg        zero_o,
   output reg        ready_o
);

  localparam EXP_WIDTH = 8;
  localparam FRAC_WIDTH = 23;

    // rounding mode isn't require piplinization
  wire rm_nearest = (rmode_i==2'b00);
  wire rm_to_zero = (rmode_i==2'b01);
  wire rm_to_infp = (rmode_i==2'b10);
  wire rm_to_infm = (rmode_i==2'b11);

  /*
     Any stage's output is registered.
     Definitions:
       s??o_name - "S"tage number "??", "O"utput
       s??t_name - "S"tage number "??", "T"emporary (internally)
  */

  /* Stage #1: pre-conversion operations */
  /*   makes sense mostly for f2i case      */

  wire [EXP_WIDTH-1:0]  s1t_expa = opa_i[30:23];
  wire [FRAC_WIDTH-1:0] s1t_fracta = opa_i[22:0];

    // collect operands related information
  wire s1t_signa   = opa_i[31];
  wire s1t_expa_ff = &s1t_expa;
  wire s1t_infa    = s1t_expa_ff & !(|s1t_fracta);
  wire s1t_qnan_a  = s1t_expa_ff & s1t_fracta[22];
  wire s1t_snan_a  = s1t_expa_ff & (!s1t_fracta[22] & (|s1t_fracta[21:0]));
    // opa is denormalized
  wire s1t_opa_dn = !(|s1t_expa);

   // direction of conversion
  wire s1t_f2i = (fpu_op_i == 3'b101);

    // start conversion
  wire [EXP_WIDTH-1:0] s1t_exp8 = (s1t_f2i ? s1t_expa : {EXP_WIDTH{1'b0}});
  wire [FRAC_WIDTH:0] s1t_fracta_24 = {!s1t_opa_dn,s1t_fracta}; // restores hidden "1"
  
  wire [47:0] s1t_fract48 =
    s1t_f2i ?
      (s1t_signa ?  1-{24'd0,s1t_fracta_24}-1 : {24'd0,s1t_fracta_24}) :
      (s1t_signa ?  1-{opa_i,17'd1} : {opa_i,17'd0});

  // Special case of largest negative integer we can convert to - usually
  // gets picked up as invalid, but really it's not, so deal with it as a
  // special case.
  wire s1t_f2i_no_inv_special = (opa_i == 32'hcf000000);
  
  // stage #1 outputs
  //   input related
  reg s1o_infa, s1o_qnan_a, s1o_snan_a;
  //   computation related
  reg s1o_signa;
  reg [EXP_WIDTH-1:0] s1o_exp8;
  reg [47:0]  s1o_fract48;
  reg s1o_f2i;
  reg s1o_f2i_no_inv_special;

  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s1o_infa  <= s1t_infa;
      s1o_qnan_a <= s1t_qnan_a;
      s1o_snan_a <= s1t_snan_a;
        // computation related
      s1o_signa <= s1t_signa;
      s1o_exp8 <= s1t_exp8;
      s1o_fract48 <= s1t_fract48;
      s1o_f2i <= s1t_f2i;
      s1o_f2i_no_inv_special <= s1t_f2i_no_inv_special;
    end // (reset or flush) / advance
  end // posedge clock

  // ready is special case
  reg s1o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      s1o_ready <= 0;
    else if(adv_i)
      s1o_ready <= start_i;
  end // posedge clock

  /*
    Stages #2, #3, #4
      Conversion and normalization (for i2f)
  */

  /* Stage #2 */

    // Count Leading zeros in fraction
  reg [5:0] s2t_ldz;
  always @(s1o_fract48)
    casez(s1o_fract48)  // synopsys full_case parallel_case
      48'b1???????????????????????????????????????????????: s2t_ldz =  1;
      48'b01??????????????????????????????????????????????: s2t_ldz =  2;
      48'b001?????????????????????????????????????????????: s2t_ldz =  3;
      48'b0001????????????????????????????????????????????: s2t_ldz =  4;
      48'b00001???????????????????????????????????????????: s2t_ldz =  5;
      48'b000001??????????????????????????????????????????: s2t_ldz =  6;
      48'b0000001?????????????????????????????????????????: s2t_ldz =  7;
      48'b00000001????????????????????????????????????????: s2t_ldz =  8;
      48'b000000001???????????????????????????????????????: s2t_ldz =  9;
      48'b0000000001??????????????????????????????????????: s2t_ldz =  10;
      48'b00000000001?????????????????????????????????????: s2t_ldz =  11;
      48'b000000000001????????????????????????????????????: s2t_ldz =  12;
      48'b0000000000001???????????????????????????????????: s2t_ldz =  13;
      48'b00000000000001??????????????????????????????????: s2t_ldz =  14;
      48'b000000000000001?????????????????????????????????: s2t_ldz =  15;
      48'b0000000000000001????????????????????????????????: s2t_ldz =  16;
      48'b00000000000000001???????????????????????????????: s2t_ldz =  17;
      48'b000000000000000001??????????????????????????????: s2t_ldz =  18;
      48'b0000000000000000001?????????????????????????????: s2t_ldz =  19;
      48'b00000000000000000001????????????????????????????: s2t_ldz =  20;
      48'b000000000000000000001???????????????????????????: s2t_ldz =  21;
      48'b0000000000000000000001??????????????????????????: s2t_ldz =  22;
      48'b00000000000000000000001?????????????????????????: s2t_ldz =  23;
      48'b000000000000000000000001????????????????????????: s2t_ldz =  24;
      48'b0000000000000000000000001???????????????????????: s2t_ldz =  25;
      48'b00000000000000000000000001??????????????????????: s2t_ldz =  26;
      48'b000000000000000000000000001?????????????????????: s2t_ldz =  27;
      48'b0000000000000000000000000001????????????????????: s2t_ldz =  28;
      48'b00000000000000000000000000001???????????????????: s2t_ldz =  29;
      48'b000000000000000000000000000001??????????????????: s2t_ldz =  30;
      48'b0000000000000000000000000000001?????????????????: s2t_ldz =  31;
      48'b00000000000000000000000000000001????????????????: s2t_ldz =  32;
      48'b000000000000000000000000000000001???????????????: s2t_ldz =  33;
      48'b0000000000000000000000000000000001??????????????: s2t_ldz =  34;
      48'b00000000000000000000000000000000001?????????????: s2t_ldz =  35;
      48'b000000000000000000000000000000000001????????????: s2t_ldz =  36;
      48'b0000000000000000000000000000000000001???????????: s2t_ldz =  37;
      48'b00000000000000000000000000000000000001??????????: s2t_ldz =  38;
      48'b000000000000000000000000000000000000001?????????: s2t_ldz =  39;
      48'b0000000000000000000000000000000000000001????????: s2t_ldz =  40;
      48'b00000000000000000000000000000000000000001???????: s2t_ldz =  41;
      48'b000000000000000000000000000000000000000001??????: s2t_ldz =  42;
      48'b0000000000000000000000000000000000000000001?????: s2t_ldz =  43;
      48'b00000000000000000000000000000000000000000001????: s2t_ldz =  44;
      48'b000000000000000000000000000000000000000000001???: s2t_ldz =  45;
      48'b0000000000000000000000000000000000000000000001??: s2t_ldz =  46;
      48'b00000000000000000000000000000000000000000000001?: s2t_ldz =  47;
      48'b00000000000000000000000000000000000000000000000?: s2t_ldz =  48;
    endcase

  // calculate shift value
  wire [7:0] s2t_f2i_shft = s1o_exp8 - 8'h7d; // in-125
  wire [7:0] s2t_cnv_shft = s1o_f2i ?
    (s2t_f2i_shft & {8{!(|s2t_f2i_shft[7:6])}}) : {2'h0, s2t_ldz};

  wire s2t_fract48_00 = !(|s1o_fract48);

  wire [7:0] s2t_exp_i2f = s2t_fract48_00 ?
    (s1o_signa ? 8'h9e : 0) : (8'h9e - {2'd0,s2t_ldz});


  // stage #2 outputs
  //   input related
  reg s2o_infa, s2o_qnan_a, s2o_snan_a;
  //   computation related
  reg s2o_signa;
  reg [EXP_WIDTH-1:0] s2o_exp8;
  reg [47:0]  s2o_fract48;
  reg s2o_fract48_00;
  reg [5:0] s2o_cnv_shft;
  reg [7:0] s2o_exp_i2f;
  reg [5:0] s2o_ldz;
  reg s2o_f2i;
  reg s2o_f2i_no_inv_special;

  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s2o_infa  <= s1o_infa;
      s2o_qnan_a <= s1o_qnan_a;
      s2o_snan_a <= s1o_snan_a;
        // computation related
      s2o_signa <= s1o_signa;
      s2o_exp8 <= s1o_exp8;
      s2o_fract48 <= s1o_fract48;
      s2o_fract48_00 <= s2t_fract48_00;
      s2o_cnv_shft <= s2t_cnv_shft[5:0];
      s2o_exp_i2f <= s2t_exp_i2f;
      s2o_ldz <= s2t_ldz;
      s2o_f2i <= s1o_f2i;
      s2o_f2i_no_inv_special <= s1o_f2i_no_inv_special;
    end // advance
  end // posedge clock

  // ready is special case
  reg s2o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      s2o_ready <= 0;
    else if(adv_i)
      s2o_ready <= s1o_ready;
  end // posedge clock


  /* Stage #3: raction shift and exponent normalization */

  // Misc common signals
  wire s3t_exp_in_ff = &s2o_exp8;
  wire s3t_exp_in_00 = !(|s2o_exp8);
  
  wire s3t_nan_a = s2o_qnan_a | s2o_snan_a;

  wire s3t_carry = s2o_fract48[47];

  // ---------------------------------------------------------------------
  // Fraction Normalization

  // For F2I conversion we can move point right on 30-bits maximum
  // 23-bits of mantissa + 7 bits of exp, while other 2 bits are:
  //  1) implicit "1" in normalized values
  //  2) "sign" placed into its position outside of the function
  localparam  f2i_emax = 8'h9d; // 157

  // Special Signals for f2i
  wire [7:0] f2i_emin = rm_nearest ? 8'h7e : 8'h7f; // (<126) : (<127)

  wire s3t_f2i_exp_gt_max = (s2o_exp8 > f2i_emax);
  wire s3t_f2i_exp_lt_min = (s2o_exp8 < f2i_emin);

  // Minimum (largest possible -int : 0x80000000
  // a) too big exp. and negative sign - result will be largest possible -int
  // b) -infinity: largest possible -int
  wire s3t_f2i_min =
         (s3t_f2i_exp_gt_max & s2o_signa & !s3t_exp_in_ff) |
         (s2o_infa & s2o_signa);

  // Zero or largest -int cases
  wire s3t_f2i_zero =
     s3t_f2i_min |                                    // largest possible -int (all zeros except sign)
     (s2o_fract48_00 & s3t_exp_in_00) |               // +/- 0.0 cases
     (rm_to_infm & !s2o_signa & s3t_f2i_exp_lt_min) | // to INF- & 0<f<1.0
     (rm_to_zero & s3t_f2i_exp_lt_min) |              // to zero & |f|<1.0
     (rm_to_infp & s2o_signa & s3t_f2i_exp_lt_min) |  // to INF+ & (-1.0)<f<0
     (rm_nearest & s3t_f2i_exp_lt_min);               // to nearest & |f|<0.5: see selection for lt<min earlear


  // Maximum :
  // a) disabled when the -0.0 case comes up
  // b) +/- NaN or +inf - result will be maximum int
  // c) too big exp and positive sign - result will be maximum int.
  // d) rounding negative down and less than minimum expon. for int = -1
  wire s3t_f2i_max =
    !(s2o_fract48_00 & s3t_exp_in_00) &                  // disable +/- 0.0 cases
    (
      (s3t_nan_a | (s2o_infa & !s2o_signa)) |            // Either +/- NaN, or +inf
      (!s2o_signa & s3t_f2i_exp_gt_max & !s3t_exp_in_ff) // too big positive => maximum int
    );

  // shift fraction part
  wire [47:0] s3t_fract48_shftl =
    (s2o_f2i & s3t_f2i_zero) ? 0 : (s2o_fract48 << s2o_cnv_shft);


  // ---------------------------------------------------------------------
  // Exponent Normalization
  wire [8:0] s3t_exp_next_mi = s2o_exp8 - {3'd0,s2o_ldz} + 9'd2; // 9 bits - includes carry out

  // Fasu Output will be denormalized
  wire s3t_dn = (s3t_exp_in_00 | (s3t_exp_next_mi[8] & !s3t_carry));

  wire [8:0] s3t_exp9 = s2o_exp8 + 8'd1;
  wire s3t_exp_out1_co = s3t_carry ? s3t_exp9[8] : s3t_exp_next_mi[8];

  wire [55:0] s3t_exp_f2i_1 = {{8{s3t_carry}},s2o_fract48} << s2o_cnv_shft;
  wire [7:0]  s3t_exp_f2i   = s3t_f2i_zero ? 0 :
                              s3t_f2i_max ? 8'hff :
                              s3t_exp_f2i_1[55:48];
                              
  wire [7:0] s3t_exp_out  = s2o_f2i ? s3t_exp_f2i : s2o_exp_i2f;


  // ---------------------------------------------------------------------
  wire s3t_fract23_in_nz = |s2o_fract48[22:0];


  // stage #3 outputs
  //   input related
  reg s3o_infa, s3o_qnan_a, s3o_snan_a;
  //   computation related
  reg s3o_signa;
  reg [EXP_WIDTH-1:0] s3o_exp8;
  reg s3o_f2i_exp_gt_max;
  reg [22:0] s3o_fract23;
  reg s3o_r, s3o_s;
  reg s3o_fract48_00;
  reg s3o_fract23_in_nz;
  reg s3o_carry;
  reg [7:0] s3o_exp_out;
  reg [7:0] s3o_exp_next_mi;
  reg s3o_exp_out1_co;
  reg s3o_dn;
  reg s3o_f2i_min, s3o_f2i_zero, s3o_f2i_max;
  reg s3o_f2i;
  reg s3o_f2i_no_inv_special;

  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s3o_infa  <= s2o_infa;
      s3o_qnan_a <= s2o_qnan_a;
      s3o_snan_a <= s2o_snan_a;
        // computation related
      s3o_signa <= s2o_signa;
      s3o_exp8 <= s2o_exp8;
      s3o_f2i_exp_gt_max <= s3t_f2i_exp_gt_max;
      s3o_fract23 <= s3t_fract48_shftl[47:25];
      s3o_r <= s3t_fract48_shftl[24];
      s3o_s <= |s3t_fract48_shftl[23:0];
      s3o_fract48_00 <= s2o_fract48_00;
      s3o_fract23_in_nz <= s3t_fract23_in_nz;
      s3o_carry <= s3t_carry;
      s3o_exp_out <= s3t_exp_out;
      s3o_exp_next_mi <= s3t_exp_next_mi[7:0];
      s3o_exp_out1_co <= s3t_exp_out1_co;
      s3o_dn <= s3t_dn;
      s3o_f2i_min <= s3t_f2i_min;
      s3o_f2i_zero <= s3t_f2i_zero;
      s3o_f2i_max <= s3t_f2i_max;
      s3o_f2i <= s2o_f2i;
      s3o_f2i_no_inv_special <= s2o_f2i_no_inv_special;
    end // advance
  end // posedge clock

  // ready is special case
  reg s3o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      s3o_ready <= 0;
    else if(adv_i)
      s3o_ready <= s2o_ready;
  end // posedge clock


  /* Stage #4: round and output */

  // ---------------------------------------------------------------------
  // Round
  wire s4t_exp_in_ff = &s3o_exp8;
  wire s4t_exp_in_00 = !(|s3o_exp8);
  
  wire s4t_exp_out_ff = &s3o_exp_out;
  wire s4t_exp_out_00 = !(|s3o_exp_out);
  wire s4t_exp_out_fe = &s3o_exp_out[7:1] & (!s3o_exp_out[0]);

  wire s4t_fract23_7fffff = &s3o_fract23;
  wire s4t_fract23_00     = !(|s3o_fract23);

  wire [7:0] s4t_exp_out_pl1 = s3o_exp_out + 1;
  wire [23:0] s4t_fract23_pl1 = s3o_fract23 + 1;// Incremented fraction for rounding

   // Extract rounding (GRS) bits
  wire s4t_g  = s3o_fract23[0];
  wire s4t_rs = s3o_r | s3o_s;

  // Round to nearest even
  wire s4t_round = (s4t_g & s3o_r) | (s3o_r & s3o_s) ;

  wire s4t_exp_rnd_adj0;
  wire [22:0] s4t_fract23_rnd0;
  wire [7:0] s4t_exp_out_rnd0;
  
  assign {s4t_exp_rnd_adj0, s4t_fract23_rnd0} = s4t_round ?
   s4t_fract23_pl1 : {1'b0, s3o_fract23};

  assign s4t_exp_out_rnd0 = s4t_exp_rnd_adj0 ?
    s4t_exp_out_pl1 : s3o_exp_out;

  // round to zero
  // Added detection of sign and rounding up in case of negative ftoi! - JPB
  wire [22:0] s4t_fract23_rnd1;
  wire [7:0] s4t_exp_out_rnd1;
  
  assign s4t_fract23_rnd1 =
    (s4t_exp_out_ff & !s3o_dn & !s3o_f2i) ? 23'h7fffff :
    (s3o_f2i & s4t_rs & s3o_signa) ? s4t_fract23_pl1[22:0] :
    s3o_fract23;

  assign s4t_exp_out_rnd1 =
     (s4t_g & s3o_r & s3o_s & s4t_exp_in_ff) ? s3o_exp_next_mi :
     (s4t_exp_out_ff & !s3o_f2i) ? s3o_exp8 :
     (s3o_f2i & s3o_signa & s4t_rs & s4t_fract23_pl1[23]) ? s4t_exp_out_pl1 :
     s3o_exp_out;

  // round to +inf (UP) and -inf (DOWN)
  wire s4t_sign = rm_to_infm ? (!s3o_signa) : s3o_signa;

  wire s4t_round2a = (!s4t_exp_out_fe) | (!s4t_fract23_7fffff) |
                     (s4t_exp_out_fe & s4t_fract23_7fffff);

  wire s4t_round2_fasu = (s4t_rs & !s4t_sign) &
                         (!s3o_exp_out[7] | (s3o_exp_out[7] & s4t_round2a));

  // select fract-out+1 if: to INF+ & ((R|S) | denormalized_positive)
  wire s4t_round2_f2i =
     rm_to_infp & (s4t_rs | (!s3o_signa & s4t_exp_in_00 & s3o_fract23_in_nz));

  wire s4t_round2 = s3o_f2i ? s4t_round2_f2i : s4t_round2_fasu;

  wire s4t_exp_rnd_adj2a;
  wire [22:0] s4t_fract23_rnd2a;
  wire [7:0] s4t_exp_out_rnd2a;
  
  assign {s4t_exp_rnd_adj2a, s4t_fract23_rnd2a} =
    s4t_round2 ? s4t_fract23_pl1 : {1'b0, s3o_fract23};

  assign s4t_exp_out_rnd2a =
    s4t_exp_rnd_adj2a ? s4t_exp_out_pl1 : s3o_exp_out;

  wire [22:0] s4t_fract23_rnd2;
  wire [7:0] s4t_exp_out_rnd2;

  assign s4t_fract23_rnd2 =
    (s4t_sign & s4t_exp_out_ff & !s3o_dn & !s3o_f2i) ?
      23'h7fffff : s4t_fract23_rnd2a;

  assign s4t_exp_out_rnd2   =
    (s4t_sign & s4t_exp_out_ff & !s3o_f2i) ?
      8'hfe : s4t_exp_out_rnd2a;


  reg [7:0] s4t_exp_out_rnd;
  always @(rmode_i or s4t_exp_out_rnd0 or s4t_exp_out_rnd1 or s4t_exp_out_rnd2)
    case(rmode_i)  // synopsys full_case parallel_case
      0: s4t_exp_out_rnd = s4t_exp_out_rnd0;
      1: s4t_exp_out_rnd = s4t_exp_out_rnd1;
      2,3: s4t_exp_out_rnd = s4t_exp_out_rnd2;
    endcase

  reg [22:0] s4t_fract23_rnd;
  always @(rmode_i or s4t_fract23_rnd0 or s4t_fract23_rnd1 or s4t_fract23_rnd2)
    case(rmode_i)  // synopsys full_case parallel_case
      0: s4t_fract23_rnd = s4t_fract23_rnd0;
      1: s4t_fract23_rnd = s4t_fract23_rnd1;
      2,3: s4t_fract23_rnd = s4t_fract23_rnd2;
    endcase

  // ---------------------------------------------------------------------
  // Final Output Mux
  // Fix Output for denormalized and special numbers
  wire [7:0] s4t_exp_out_final = (s3o_f2i_max & s3o_f2i) ?
                                   8'hff : s4t_exp_out_rnd;

  wire s4t_exp_out_final_ff = &s4t_exp_out_final;

  wire [22:0] s4t_fract23_final =
    (s4t_exp_out_final_ff & !rm_to_zero & !s3o_f2i) ? 23'h0 :
    (s3o_f2i_max & s3o_f2i) ? 23'h7fffff :
    s4t_fract23_rnd;


  // ---------------------------------------------------------------------
  // Pack Result

  wire [30:0] s4t_out31 = {s4t_exp_out_final, s4t_fract23_final};
  wire s4t_out31_00 = !(|s4t_out31);

  wire s4t_opa_nan = s3o_qnan_a | s3o_snan_a;

  // Only ever force positive if:
  // i) It's a NaN
  // ii) It's zero and not -inf
  // iii) We've rounded to 0 (both fract and exp out are 0 and not forced)
  // Force to 1 (negative) when have negative sign with too big exponent
  wire s4t_f2i_out_sign =
    s3o_f2i_min ? 1 : // too big negative
    (s4t_opa_nan | (s3o_f2i_zero & !s3o_f2i_max) |
     (s4t_out31_00 & !s3o_f2i_zero)) ? 0 :
    s3o_signa;

  // ---------------------------------------------------------------------
  // Exceptions

  wire s4t_udf = (!s3o_carry & s3o_exp_out1_co) & !s3o_dn; // underflow

  wire s4t_inv = s3o_f2i & s3o_f2i_exp_gt_max;

  wire s4t_exp_in_lt_half = (s3o_exp8 < 8'h80);

  wire s4t_f2i_ine =
    !s4t_inv & // report either invalid or inexant
    (
      s4t_rs |
      (s3o_f2i_zero & !s3o_fract48_00 & !s3o_signa) |
      (s3o_f2i_zero & s4t_exp_in_lt_half & s3o_signa & !s3o_fract48_00) |
      (s3o_f2i_max & rm_to_infm & s4t_exp_in_lt_half)
    );

  wire s4t_ine = s3o_f2i ? s4t_f2i_ine : s4t_rs;


  // ---------------------------------------------------------------------
  // Output registers
  always @(posedge clk) begin
    if(adv_i) begin
      out_o <= s3o_f2i ? {s4t_f2i_out_sign,s4t_out31} :
                         {s3o_signa,s4t_out31};
      snan_o <= s3o_f2i & s3o_snan_a;  // Only signal sNaN when f2i
      ine_o <= s4t_ine;
      inv_o <= s4t_inv & (!s3o_f2i_no_inv_special);
      underflow_o <= s4t_udf & (!(s4t_opa_nan | s3o_infa));
      zero_o <= s3o_f2i ? (s4t_out31_00 & (!s4t_opa_nan)) :
                          (s4t_out31_00 & (!(s4t_opa_nan | s3o_infa)));      
    end // advance
  end // posedge clock

  // ready is special case
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      ready_o <= 0;
    else if(adv_i)
      ready_o <= s3o_ready;
  end // posedge clock

endmodule // pfpu32_intfloat_conv
