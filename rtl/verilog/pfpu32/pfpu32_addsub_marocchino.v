//////////////////////////////////////////////////////////////////////
//                                                                  //
//    pfpu32_addsub_marocchino                                      //
//                                                                  //
//    This file is part of the mor1kx project                       //
//    https://github.com/openrisc/mor1kx                            //
//                                                                  //
//    Description                                                   //
//    addition/subtraction pipeline for single precision floating   //
//    point numbers for MAROCCHINO pipeline                         //
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
//  Copyright (C) 2006, 2010, 2014 - 2016                           //
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


module pfpu32_addsub_marocchino
(
  // clocks and resets
  input             clk,
  input             rst,
  // ADD/SUB pipe controls
  input             pipeline_flush_i,
  input             start_i,
  input             is_sub_i,         // 1: substruction, 0: addition
  output            add_takes_op_o,
  output reg        add_rdy_o,        // ready
  input             rnd_taking_add_i,
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
  output reg        add_sign_o,      // signum
  output reg        add_sub_0_o,     // flag that actual substruction is performed and result is zero
  output reg  [4:0] add_shl_o,       // do left shift in align stage
  output reg  [9:0] add_exp10shl_o,  // exponent for left shift align
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


  // ADD/SUB pipe controls
  //  ## ready flags of stages
  reg s1o_ready;
  reg s2o_ready;
  //  ## per stage busy flags
  wire s3_busy = add_rdy_o & ~rnd_taking_add_i;
  wire s2_busy = s2o_ready & s3_busy;
  wire s1_busy = s1o_ready & s2_busy;
  //  ## per stage advance
  wire s1_adv  = start_i   & ~s1_busy;
  wire s2_adv  = s1o_ready & ~s2_busy;
  wire s3_adv  = s2o_ready & ~s3_busy;

  // ADD/SUB pipe takes operands for computation
  assign add_takes_op_o = s1_adv;


  /* Stage #1: pre addition / substraction align */

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
    if (s1_adv) begin
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
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      s1o_ready <= 1'b0;
    else if (pipeline_flush_i)
      s1o_ready <= 1'b0;
    else if (s1_adv)
      s1o_ready <= 1'b1;
    else if (s2_adv)
      s1o_ready <= 1'b0;
  end // posedge clock


  /* Stage 2: multiplex and shift */


  // shifter
  wire [25:0] s2t_fract26_fsh = {s1o_fract24_fsh,2'd0};
  wire [25:0] s2t_fract26_shr = s2t_fract26_fsh >> s1o_shr;

  // sticky
  reg s2t_sticky;
  always @(s1o_shr or s1o_fract24_fsh) begin
    case (s1o_shr)
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
    if (s2_adv) begin
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
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      s2o_ready <= 1'b0;
    else if (pipeline_flush_i)
      s2o_ready <= 1'b0;
    else if (s2_adv)
      s2o_ready <= 1'b1;
    else if (s3_adv)
      s2o_ready <= 1'b0;
  end // posedge clock


  /* Stage 4: update exponent */


  // for possible left shift
  // [26] bit is right shift flag
  reg [4:0] s3t_nlz;
  always @(s2o_fract27) begin
    casez (s2o_fract27)
      27'b1??????????????????????????: s3t_nlz =  0; // [26] bit: shift right
      27'b01?????????????????????????: s3t_nlz =  0; // 1 is in place
      27'b001????????????????????????: s3t_nlz =  1;
      27'b0001???????????????????????: s3t_nlz =  2;
      27'b00001??????????????????????: s3t_nlz =  3;
      27'b000001?????????????????????: s3t_nlz =  4;
      27'b0000001????????????????????: s3t_nlz =  5;
      27'b00000001???????????????????: s3t_nlz =  6;
      27'b000000001??????????????????: s3t_nlz =  7;
      27'b0000000001?????????????????: s3t_nlz =  8;
      27'b00000000001????????????????: s3t_nlz =  9;
      27'b000000000001???????????????: s3t_nlz = 10;
      27'b0000000000001??????????????: s3t_nlz = 11;
      27'b00000000000001?????????????: s3t_nlz = 12;
      27'b000000000000001????????????: s3t_nlz = 13;
      27'b0000000000000001???????????: s3t_nlz = 14;
      27'b00000000000000001??????????: s3t_nlz = 15;
      27'b000000000000000001?????????: s3t_nlz = 16;
      27'b0000000000000000001????????: s3t_nlz = 17;
      27'b00000000000000000001???????: s3t_nlz = 18;
      27'b000000000000000000001??????: s3t_nlz = 19;
      27'b0000000000000000000001?????: s3t_nlz = 20;
      27'b00000000000000000000001????: s3t_nlz = 21;
      27'b000000000000000000000001???: s3t_nlz = 22;
      27'b0000000000000000000000001??: s3t_nlz = 23;
      27'b00000000000000000000000001?: s3t_nlz = 24;
      27'b000000000000000000000000001: s3t_nlz = 25;
      27'b000000000000000000000000000: s3t_nlz =  0; // zero result
    endcase
  end // always

  // left shift amount and corrected exponent
  wire [4:0] s3t_nlz_m1    = (s3t_nlz - 5'd1);
  wire [9:0] s3t_exp10c_m1 = s2o_exp10c - 10'd1;
  wire [9:0] s3t_exp10c_mz = s2o_exp10c - {5'd0,s3t_nlz};
  wire [4:0] s3t_shl;
  wire [9:0] s3t_exp10shl;
  assign {s3t_shl,s3t_exp10shl} =
      // shift isn't needed or impossible
    (~(|s3t_nlz) | (s2o_exp10c == 10'd1)) ?
                              {5'd0,s2o_exp10c} :
      // normalization is possible
    (s2o_exp10c >  s3t_nlz) ? {s3t_nlz,s3t_exp10c_mz} :
      // denormalized cases
    (s2o_exp10c == s3t_nlz) ? {s3t_nlz_m1,10'd1} :
                              {s3t_exp10c_m1[4:0],10'd1};


  // registering output
  always @(posedge clk) begin
    if (s3_adv) begin
        // input related
      add_inv_o       <= s2o_inv;
      add_inf_o       <= s2o_inf_i;
      add_snan_o      <= s2o_snan_i;
      add_qnan_o      <= s2o_qnan_i;
      add_anan_sign_o <= s2o_anan_i_sign;
        // computation related
      add_sign_o      <= s2o_signc;
      add_sub_0_o     <= s2o_sub_0;
      add_shl_o       <= s3t_shl;
      add_exp10shl_o  <= s3t_exp10shl;
      add_exp10sh0_o  <= s2o_exp10c;
      add_fract28_o   <= {s2o_fract27,s2o_sticky};
    end // advance
  end // posedge clock

  // ready is special case
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      add_rdy_o <= 1'b0;
    else if (pipeline_flush_i)
      add_rdy_o <= 1'b0;
    else if (s3_adv)
      add_rdy_o <= 1'b1;
    else if (rnd_taking_add_i)
      add_rdy_o <= 1'b0;
  end // posedge clock

endmodule // pfpu32_addsub_marocchino
