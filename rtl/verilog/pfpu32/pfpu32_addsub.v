//////////////////////////////////////////////////////////////////////
//                                                                  //
//    pfpu32_addsub                                                 //
//                                                                  //
//    This file is part of the mor1kx project                       //
//    https://github.com/openrisc/mor1kx                            //
//                                                                  //
//    Description                                                   //
//    addition/subtraction pipeline for single precision floating   //
//    point numbers                                                 //
//                                                                  //
//    Author(s):                                                    //
//        - Original design (FPU100) -                              //
//          Jidan Al-eryani, jidan@gmx.net                          //
//        - Conv. to Verilog and inclusion in OR1200 -              //
//          Julius Baxter, julius@opencores.org                     //
//        - Update for mor1kx,                                      //
//          bug fixing and further development -                    //
//          Andrey Bacherov, avbacherov@opencores.org               //
//                                                                  //
//////////////////////////////////////////////////////////////////////
//                                                                  //
//  Copyright (C) 2006, 2010, 2014                                  //
//                                                                  //
//  This source file may be used and distributed without            //
//  restriction provided that this copyright statement is not       //
//  removed from the file and that any derivative work contains     //
//  the original copyright notice and the associated disclaimer.    //
//                                                                  //
//    THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY           //
//  EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       //
//  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS       //
//  FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL THE AUTHOR          //
//  OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,             //
//  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES        //
//  (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE       //
//  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR            //
//  BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF      //
//  LIABILITY, WHETHER IN  CONTRACT, STRICT LIABILITY, OR TORT      //
//  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      //
//  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE             //
//  POSSIBILITY OF SUCH DAMAGE.                                     //
//////////////////////////////////////////////////////////////////////

`include "mor1kx-defines.v"


module pfpu32_addsub
(
   input             clk,
   input             rst,
   input             flush_i,  // flushe pipe
   input             adv_i,    // advance pipe
   input             start_i,  // start add/sub
   input             is_sub_i, // 1: substruction, 0: addition
   // input 'a' related values
   input             signa_i,
   input       [9:0] exp10a_i,
   input      [23:0] fract24a_i,
   input             infa_i,
   // input 'b' related values
   input             signb_i,
   input       [9:0] exp10b_i,
   input      [23:0] fract24b_i,
   input             infb_i,
   // 'a'/'b' related
   input             snan_i,
   input             qnan_i,
   input             anan_sign_i,
   input             addsub_agtb_i,
   input             addsub_aeqb_i,
   // outputs
   output reg        add_rdy_o,       // ready
   output reg        add_sign_o,      // signum
   output reg        add_sub_0_o,     // flag that actual substruction is performed and result is zero
   output reg        add_shr_o,       // do right shift in align stage
   output reg  [4:0] add_shl_o,       // do left shift in align stage
   output reg  [9:0] add_exp10sh0_o,  // exponent for no shift in align
   output reg [27:0] add_fract28_o,   // fractional with appended {r,s} bits
   output reg        add_inv_o,       // invalid operation flag
   output reg        add_inf_o,       // infinity output reg
   output reg        add_snan_o,      // signaling NaN output reg
   output reg        add_qnan_o,      // quiet NaN output reg
   output reg        add_anan_sign_o  // signum for output nan
);
  /*
     Any stage's output is registered.
     Definitions:
       s??o_name - "S"tage number "??", "O"utput
       s??t_name - "S"tage number "??", "T"emporary (internally)
  */

  /* Stage #1: pre addition / substruction align */

    // detection of some exceptions
    //   inf - inf -> invalid operation; snan output
  wire s1t_inv = infa_i & infb_i &
                 (signa_i ^ (is_sub_i ^ signb_i));
    //   inf input
  wire s1t_inf_i = infa_i | infb_i;

    // signums for calculation
  wire s1t_calc_signa = signa_i;
  wire s1t_calc_signb = (signb_i ^ is_sub_i);

    // not shifted operand and its signum
  wire [23:0] s1t_fract24_nsh =
    addsub_agtb_i ? fract24a_i : fract24b_i;

    // operand for right shift
  wire [23:0] s1t_fract24_fsh =
    addsub_agtb_i ? fract24b_i : fract24a_i;

    // shift amount
  wire [9:0] s1t_exp_diff =
    addsub_agtb_i ? (exp10a_i - exp10b_i) :
                    (exp10b_i - exp10a_i);

  // limiter by 31
  wire [4:0] s1t_shr = s1t_exp_diff[4:0] | {5{|s1t_exp_diff[9:5]}};

  // stage #1 outputs
  //  input related
  reg s1o_inv, s1o_inf_i,
      s1o_snan_i, s1o_qnan_i, s1o_anan_i_sign;
  //  computation related
  reg        s1o_aeqb;
  reg  [4:0] s1o_shr;
  reg        s1o_sign_nsh;
  reg        s1o_op_sub;
  reg  [9:0] s1o_exp10c;
  reg [23:0] s1o_fract24_nsh;
  reg [23:0] s1o_fract24_fsh;
  //  registering
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s1o_inv         <= s1t_inv;
      s1o_inf_i       <= s1t_inf_i;
      s1o_snan_i      <= snan_i;
      s1o_qnan_i      <= qnan_i;
      s1o_anan_i_sign <= anan_sign_i;
        // computation related
      s1o_aeqb        <= addsub_aeqb_i;
      s1o_shr         <= s1t_shr & {5{~s1t_inf_i}};
      s1o_sign_nsh    <= addsub_agtb_i ? s1t_calc_signa : s1t_calc_signb;
      s1o_op_sub      <= s1t_calc_signa ^ s1t_calc_signb;
      s1o_exp10c      <= addsub_agtb_i ? exp10a_i : exp10b_i;
      s1o_fract24_nsh <= s1t_fract24_nsh & {24{~s1t_inf_i}};
      s1o_fract24_fsh <= s1t_fract24_fsh & {24{~s1t_inf_i}};
    end // advance
  end // posedge clock

  // ready is special case
  reg s1o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      s1o_ready  <= 0;
    else if(flush_i)
      s1o_ready  <= 0;
    else if(adv_i)
      s1o_ready <= start_i;
  end // posedge clock


  /* Stage 2: multiplex and shift */


  // shifter
  wire [25:0] s2t_fract26_fsh = {s1o_fract24_fsh,2'd0};
  wire [25:0] s2t_fract26_shr = s2t_fract26_fsh >> s1o_shr;

  // sticky
  reg s2t_sticky;
  always @(s1o_shr or s1o_fract24_fsh) begin
    case(s1o_shr)
      5'd0, 5'd1, 5'd2 : s2t_sticky = 1'b0; // two added zero bits
      5'd3 : s2t_sticky = s1o_fract24_fsh[0];
      5'd4 : s2t_sticky = |s1o_fract24_fsh[1:0];
      5'd5 : s2t_sticky = |s1o_fract24_fsh[2:0];
      5'd6 : s2t_sticky = |s1o_fract24_fsh[3:0];
      5'd7 : s2t_sticky = |s1o_fract24_fsh[4:0];
      5'd8 : s2t_sticky = |s1o_fract24_fsh[5:0];
      5'd9 : s2t_sticky = |s1o_fract24_fsh[6:0];
      5'd10: s2t_sticky = |s1o_fract24_fsh[7:0];
      5'd11: s2t_sticky = |s1o_fract24_fsh[8:0];
      5'd12: s2t_sticky = |s1o_fract24_fsh[9:0];
      5'd13: s2t_sticky = |s1o_fract24_fsh[10:0];
      5'd14: s2t_sticky = |s1o_fract24_fsh[11:0];
      5'd15: s2t_sticky = |s1o_fract24_fsh[12:0];
      5'd16: s2t_sticky = |s1o_fract24_fsh[13:0];
      5'd17: s2t_sticky = |s1o_fract24_fsh[14:0];
      5'd18: s2t_sticky = |s1o_fract24_fsh[15:0];
      5'd19: s2t_sticky = |s1o_fract24_fsh[16:0];
      5'd20: s2t_sticky = |s1o_fract24_fsh[17:0];
      5'd21: s2t_sticky = |s1o_fract24_fsh[18:0];
      5'd22: s2t_sticky = |s1o_fract24_fsh[19:0];
      5'd23: s2t_sticky = |s1o_fract24_fsh[20:0];
      5'd24: s2t_sticky = |s1o_fract24_fsh[21:0];
      5'd25: s2t_sticky = |s1o_fract24_fsh[22:0];
      default: s2t_sticky = |s1o_fract24_fsh[23:0];
    endcase
  end

    // add/sub of non-shifted and shifted operands
  wire [27:0] s2t_fract28_shr = {1'b0,s2t_fract26_shr,s2t_sticky};

  wire [27:0] s2t_fract28_add = {1'b0,s1o_fract24_nsh,3'd0} +
                                (s2t_fract28_shr ^ {28{s1o_op_sub}}) +
                                {27'd0,s1o_op_sub};


  // stage #2 outputs
  //  input related
  reg s2o_inv, s2o_inf_i,
      s2o_snan_i, s2o_qnan_i, s2o_anan_i_sign;
  //  computational related
  reg        s2o_signc;
  reg [9:0]  s2o_exp10c;
  reg [26:0] s2o_fract27;
  reg        s2o_sub_0;       // actual operation is substruction and the result is zero
  reg        s2o_sticky;      // rounding support
  //  registering
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s2o_inv         <= s1o_inv;
      s2o_inf_i       <= s1o_inf_i;
      s2o_snan_i      <= s1o_snan_i;
      s2o_qnan_i      <= s1o_qnan_i;
      s2o_anan_i_sign <= s1o_anan_i_sign;
        // computation related
      s2o_signc       <= s1o_sign_nsh;
      s2o_exp10c      <= s1o_exp10c;
      s2o_fract27     <= s2t_fract28_add[27:1];
      s2o_sub_0       <= s1o_aeqb & s1o_op_sub;
      s2o_sticky      <= s2t_sticky;
    end // advance
  end // posedge clock

  // ready is special case
  reg s2o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      s2o_ready  <= 0;
    else if(flush_i)
      s2o_ready  <= 0;
    else if(adv_i)
      s2o_ready <= s1o_ready;
  end // posedge clock


  /* Stage 4: update exponent */


  // for possible left shift
  // [26] bit is right shift flag
  reg [4:0] s3t_nlz;
  always @(s2o_fract27) begin
    casez(s2o_fract27)
      27'b1??????????????????????????: s3t_nlz <=  0; // [26] bit: shift right
      27'b01?????????????????????????: s3t_nlz <=  0; // 1 is in place
      27'b001????????????????????????: s3t_nlz <=  1;
      27'b0001???????????????????????: s3t_nlz <=  2;
      27'b00001??????????????????????: s3t_nlz <=  3;
      27'b000001?????????????????????: s3t_nlz <=  4;
      27'b0000001????????????????????: s3t_nlz <=  5;
      27'b00000001???????????????????: s3t_nlz <=  6;
      27'b000000001??????????????????: s3t_nlz <=  7;
      27'b0000000001?????????????????: s3t_nlz <=  8;
      27'b00000000001????????????????: s3t_nlz <=  9;
      27'b000000000001???????????????: s3t_nlz <= 10;
      27'b0000000000001??????????????: s3t_nlz <= 11;
      27'b00000000000001?????????????: s3t_nlz <= 12;
      27'b000000000000001????????????: s3t_nlz <= 13;
      27'b0000000000000001???????????: s3t_nlz <= 14;
      27'b00000000000000001??????????: s3t_nlz <= 15;
      27'b000000000000000001?????????: s3t_nlz <= 16;
      27'b0000000000000000001????????: s3t_nlz <= 17;
      27'b00000000000000000001???????: s3t_nlz <= 18;
      27'b000000000000000000001??????: s3t_nlz <= 19;
      27'b0000000000000000000001?????: s3t_nlz <= 20;
      27'b00000000000000000000001????: s3t_nlz <= 21;
      27'b000000000000000000000001???: s3t_nlz <= 22;
      27'b0000000000000000000000001??: s3t_nlz <= 23;
      27'b00000000000000000000000001?: s3t_nlz <= 24;
      27'b000000000000000000000000001: s3t_nlz <= 25;
      27'b000000000000000000000000000: s3t_nlz <=  0; // zero result
    endcase
  end // always

  // left shift amount and corrected exponent
  wire [4:0] s3t_shl =
      // shift isn't needed or impossible
    (~(|s3t_nlz) | s2o_sub_0 | (s2o_exp10c == 10'd1)) ? 5'd0 :
      // normalization is possible
    (s2o_exp10c >  s3t_nlz) ? s3t_nlz :
      // denormalized cases
    (s2o_exp10c == s3t_nlz) ? (s3t_nlz - 5'd1) : (s2o_exp10c[4:0] - 5'd1);


  // registering output
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      add_inv_o       <= s2o_inv;
      add_inf_o       <= s2o_inf_i;
      add_snan_o      <= s2o_snan_i;
      add_qnan_o      <= s2o_qnan_i;
      add_anan_sign_o <= s2o_anan_i_sign;
        // computation related
      add_sign_o      <= s2o_signc;
      add_sub_0_o     <= s2o_sub_0;
      add_shr_o       <= s2o_fract27[26];
      add_shl_o       <= s3t_shl;
      add_exp10sh0_o  <= s2o_exp10c;
      add_fract28_o   <= {s2o_fract27,s2o_sticky};
    end // advance
  end // posedge clock

  // ready is special case
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      add_rdy_o <= 0;
    else if(flush_i)
      add_rdy_o <= 0;
    else if(adv_i)
      add_rdy_o <= s2o_ready;
  end // posedge clock

/*-------------------Formal Checking------------------*/

`ifdef FORMAL

`ifdef PFPU32_ADDSUB
`define ASSUME assume
`else
`define ASSUME assert
`endif // PFPU32_ADDSUB

  // Reset the module before formal verification.
  reg f_initialized;
  initial f_initialized = 1'b0;
  begin
    always @(posedge clk)
      f_initialized <= 1'b1;

    always @(*)
      if (!f_initialized)
        assume (rst);
      else
        assume (!rst);
  end

  // Expected output, based on inputs from the last cycle in which adv_i was
  // high.
  reg [50:0] f1_expected_output;

  // Aliases
  wire        f1_add_sign      = f1_expected_output[0];
  wire        f1_add_sub_0     = f1_expected_output[1];
  wire        f1_add_shr       = f1_expected_output[2];
  wire  [4:0] f1_add_shl       = f1_expected_output[7:3];
  wire  [9:0] f1_add_exp10sh0  = f1_expected_output[17:8];
  wire [27:0] f1_add_fract28   = f1_expected_output[45:18];
  wire        f1_add_inv       = f1_expected_output[46];
  wire        f1_add_inf       = f1_expected_output[47];
  wire        f1_add_snan      = f1_expected_output[48];
  wire        f1_add_qnan      = f1_expected_output[49];
  wire        f1_add_anan_sign = f1_expected_output[50];

  // Expected output, based on inputs from two cycles ago in which adv_i was
  // high.
  reg [50:0] f2_expected_output;

  // Expected output, based on inputs from three cycles ago in which adv_i was
  // high.
  reg [50:0] f3_expected_output;

  // Aliases
  wire        f3_add_sign      = f3_expected_output[0];
  wire        f3_add_sub_0     = f3_expected_output[1];
  wire        f3_add_shr       = f3_expected_output[2];
  wire  [4:0] f3_add_shl       = f3_expected_output[7:3];
  wire  [9:0] f3_add_exp10sh0  = f3_expected_output[17:8];
  wire [27:0] f3_add_fract28   = f3_expected_output[45:18];
  wire        f3_add_inv       = f3_expected_output[46];
  wire        f3_add_inf       = f3_expected_output[47];
  wire        f3_add_snan      = f3_expected_output[48];
  wire        f3_add_qnan      = f3_expected_output[49];
  wire        f3_add_anan_sign = f3_expected_output[50];

  // Determine whether we actually have a subtraction operation and, if so,
  // whether the subtraction yields 0.
  wire f_is_sub = signa_i ^ signb_i ^ is_sub_i;
  wire f_sub_0 = f_is_sub & addsub_aeqb_i;

  // Re-order operands so that left side is at least as large as the right.
  wire [23:0] f_fract24_l = addsub_agtb_i ? fract24a_i : fract24b_i;
  wire [23:0] f_fract24_r = addsub_agtb_i ? fract24b_i : fract24a_i;

  // Shift the right side to get it to line up with the left's exponent.
  wire [9:0] f_exp_diff =
    addsub_agtb_i ? exp10a_i - exp10b_i : exp10b_i - exp10a_i;
  wire [25:0] f_fract26_r_shifted = {f_fract24_r, 2'b0} >> f_exp_diff;

  // Figure out the sticky bit.
  wire f_sticky;
  always @(f_exp_diff or f_fract24_r) begin
    case(f_exp_diff)
      9'd0, 9'd1, 9'd2: f_sticky = 0;
      9'd3:    f_sticky = |f_fract24_r[0];
      9'd4:    f_sticky = |f_fract24_r[1:0];
      9'd5:    f_sticky = |f_fract24_r[2:0];
      9'd6:    f_sticky = |f_fract24_r[3:0];
      9'd7:    f_sticky = |f_fract24_r[4:0];
      9'd8:    f_sticky = |f_fract24_r[5:0];
      9'd9:    f_sticky = |f_fract24_r[6:0];
      9'd10:   f_sticky = |f_fract24_r[7:0];
      9'd11:   f_sticky = |f_fract24_r[8:0];
      9'd12:   f_sticky = |f_fract24_r[9:0];
      9'd13:   f_sticky = |f_fract24_r[10:0];
      9'd14:   f_sticky = |f_fract24_r[11:0];
      9'd15:   f_sticky = |f_fract24_r[12:0];
      9'd16:   f_sticky = |f_fract24_r[13:0];
      9'd17:   f_sticky = |f_fract24_r[14:0];
      9'd18:   f_sticky = |f_fract24_r[15:0];
      9'd19:   f_sticky = |f_fract24_r[16:0];
      9'd20:   f_sticky = |f_fract24_r[17:0];
      9'd21:   f_sticky = |f_fract24_r[18:0];
      9'd22:   f_sticky = |f_fract24_r[19:0];
      9'd23:   f_sticky = |f_fract24_r[20:0];
      9'd24:   f_sticky = |f_fract24_r[21:0];
      9'd25:   f_sticky = |f_fract24_r[22:0];
      default: f_sticky = |f_fract24_r[23:0];
    endcase
  end

  // Add/subtract the fractional parts.
  wire [27:0] f_fract28_l = {1'b0, f_fract24_l, 3'b0};
  wire [27:0] f_fract28_r = {1'b0, f_fract26_r_shifted, f_sticky};
  wire [27:0] f_fract28 =
    (f_is_sub ? f_fract28_l - f_fract28_r : f_fract28_l + f_fract28_r)
      | {27'b0, f_sticky};

  // Figure out how much we need to left-shift to normalize f_fract28.
  // Normalization occurs when the two highest bits are 01. Here, the
  // least-significant bit is the sticky bit, and is therefore ignored.
  reg [4:0] f_normalization_shift;
  always @(f_fract28) begin
    casez(f_fract28)
      28'b1???????????????????????????: f_normalization_shift = 5'd0; // right shift needed
      28'b01??????????????????????????: f_normalization_shift = 5'd0; // OK
      28'b001?????????????????????????: f_normalization_shift = 5'd1;
      28'b0001????????????????????????: f_normalization_shift = 5'd2;
      28'b00001???????????????????????: f_normalization_shift = 5'd3;
      28'b000001??????????????????????: f_normalization_shift = 5'd4;
      28'b0000001?????????????????????: f_normalization_shift = 5'd5;
      28'b00000001????????????????????: f_normalization_shift = 5'd6;
      28'b000000001???????????????????: f_normalization_shift = 5'd7;
      28'b0000000001??????????????????: f_normalization_shift = 5'd8;
      28'b00000000001?????????????????: f_normalization_shift = 5'd9;
      28'b000000000001????????????????: f_normalization_shift = 5'd10;
      28'b0000000000001???????????????: f_normalization_shift = 5'd11;
      28'b00000000000001??????????????: f_normalization_shift = 5'd12;
      28'b000000000000001?????????????: f_normalization_shift = 5'd13;
      28'b0000000000000001????????????: f_normalization_shift = 5'd14;
      28'b00000000000000001???????????: f_normalization_shift = 5'd15;
      28'b000000000000000001??????????: f_normalization_shift = 5'd16;
      28'b0000000000000000001?????????: f_normalization_shift = 5'd17;
      28'b00000000000000000001????????: f_normalization_shift = 5'd18;
      28'b000000000000000000001???????: f_normalization_shift = 5'd19;
      28'b0000000000000000000001??????: f_normalization_shift = 5'd20;
      28'b00000000000000000000001?????: f_normalization_shift = 5'd21;
      28'b000000000000000000000001????: f_normalization_shift = 5'd22;
      28'b0000000000000000000000001???: f_normalization_shift = 5'd23;
      28'b00000000000000000000000001??: f_normalization_shift = 5'd24;
      28'b000000000000000000000000001?: f_normalization_shift = 5'd25;
      28'b000000000000000000000000000?: f_normalization_shift = 5'd0; // zero
    endcase
  end

  // Exponent if we didn't have to shift.
  wire [9:0] f_exp10sh0 = addsub_agtb_i ? exp10a_i : exp10b_i;

  // Figure out how much the result needs to be shifted left.
  reg [4:0] f_shift_left;
  always @(f_normalization_shift or f_sub_0 or f_exp10sh0) begin
    if ((f_normalization_shift == 5'd0) | f_sub_0)
      // Shift not needed.
      f_shift_left = 5'd0;
    else if (f_exp10sh0 == 10'd1)
      // Started with denormalized values. Can't shift.
      f_shift_left = 5'd0;
    else if (f_exp10sh0 > f_normalization_shift)
      f_shift_left = f_normalization_shift;
    else
      // Creating a denormalized value.
      f_shift_left = f_exp10sh0[4:0] - 5'd1;
  end

  // Track expected output as pipeline progresses.
  always @(posedge clk) begin
    if (adv_i) begin
      // Initialize expected output for current cycle inputs.

      // If |a| > |b|, then the sign of the result is that of a. Otherwise, it
      // is that of b, after taking the operator into account.
      f1_add_sign <= addsub_agtb_i ? signa_i : signb_i ^ is_sub_i;

      // According to the contract, add_sub_0 is high iff we have an actual
      // subtraction that yields 0.
      f1_add_sub_0 <= f_sub_0;

      // If the high bit is set in the result's fractional part, then it needs
      // to be right-shifted.
      f1_add_shr <= f_fract28[27];

      f1_add_shl <= f_shift_left;
      f1_add_exp10sh0 <= f_exp10sh0;
      f1_add_fract28 <= f_fract28;

      // Subtraction of two infinities is undefined, and therefore invalid.
      f1_add_inv <= infa_i & infb_i & f_is_sub;

      // Result is an infinity if either operand is infinity.
      f1_add_inf <= infa_i | infb_i;

      // Pass-through signals.
      f1_add_snan <= snan_i;
      f1_add_qnan <= qnan_i;
      f1_add_anan_sign <= anan_sign_i;

      // Move expected output along the pipeline.
      f2_expected_output <= f1_expected_output;
      f3_expected_output <= f2_expected_output;
    end
  end

  // Assertions on output.
  always @(posedge clk) begin
    if (f_initialized) begin
      // No results should be emitted if the pipeline was flushed.
      if ($past(flush_i) || $past(flush_i,2) || $past(flush_i,3))
        assert (!add_rdy_o);

      // XXX - assuming adv_i is high for three consecutive cycles, to ensure
      // that f3_expected_output is meaningful.
      if (add_rdy_o && $past(adv_i) && $past(adv_i,2) && $past(adv_i,3)) begin
        assert (add_snan_o == f3_add_snan);
        assert (add_qnan_o == f3_add_qnan);
        assert (add_anan_sign_o == f3_add_anan_sign);

        // Assert remaining outputs only when they are meaningful.
        if (!(f3_add_snan | f3_add_qnan | f3_add_anan_sign)) begin
          assert (add_inv_o == f3_add_inv);
          if (!f3_add_inv) begin
            assert (add_inf_o == f3_add_inf);
            if (!f3_add_inf) begin
              assert (add_sign_o == f3_add_sign);
              assert (add_sub_0_o == f3_add_sub_0);
              assert (add_shr_o == f3_add_shr);
              assert (add_shl_o == f3_add_shl);
              assert (add_exp10sh0_o == f3_add_exp10sh0);
              assert (add_fract28_o == f3_add_fract28);
            end
          end
        end
      end
    end
  end

  // Verify that a result is produced after three clocks.
  generate
  begin : f_addsub_multiclock
    f_multiclock_pfpu32_op #(
      .OP_MAX_CLOCKS(3),
    ) u_f_multiclock (
      .clk(clk),
      .flush_i(flush_i),
      .adv_i(adv_i),
      .start_i(start_i),
      .result_rdy_i(add_rdy_o),
      .f_initialized(f_initialized),
    );
  end
  endgenerate

`endif // FORMAL
endmodule // pfpu32_addsub
