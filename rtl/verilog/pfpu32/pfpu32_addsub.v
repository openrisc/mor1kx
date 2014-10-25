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
   input       [1:0] rmode_i,  // round mode
   input      [31:0] opa_i,
   input      [31:0] opb_i,
   output reg [31:0] opc_o,
   output reg        ine_o,
   output reg        inv_o,    // inf-inf -> invalid flag & qnan result
   output reg        ovf_o,
   output reg        inf_o,
   output reg        unf_o,
   output reg        zer_o,    // zero rezult
   output reg        ready_o
);

  localparam INF  = 31'b1111111100000000000000000000000;
  localparam QNAN = 31'b1111111110000000000000000000000;
  localparam EXP_WIDTH = 8;
  localparam FRAC_WIDTH = 23;

  /*
     Any stage's output is registered.
     Definitions:
       s??o_name - "S"tage number "??", "O"utput
       s??t_name - "S"tage number "??", "T"emporary (internally)
  */
  
  /*
    Stages #1 and #2
    pre addition / substruction normalization
  */

  /* Stage #1 */

    // aliases
  wire s1t_signa = opa_i[31];
  wire s1t_signb = opb_i[31];
  wire [EXP_WIDTH-1 : 0]  s1t_expa = opa_i[30:23];
  wire [EXP_WIDTH-1 : 0]  s1t_expb = opb_i[30:23];
  wire [FRAC_WIDTH-1 : 0] s1t_fracta = opa_i[22:0];
  wire [FRAC_WIDTH-1 : 0] s1t_fractb = opb_i[22:0];

    // collect operands related information
  wire s1t_expa_ff = &s1t_expa;
  wire s1t_expb_ff = &s1t_expb;
  wire s1t_infa  = s1t_expa_ff & !(|s1t_fracta);
  wire s1t_infb  = s1t_expb_ff & !(|s1t_fractb);
    // signaling NaN: exponent is 8hff, [22] is zero,
    //                rest of fract is non-zero
    // quiet NaN: exponent is 8hff, [22] is 1
  wire s1t_snan_a = s1t_expa_ff & !s1t_fracta[22] & (|s1t_fracta[21:0]);
  wire s1t_qnan_a = s1t_expa_ff &  s1t_fracta[22];
  wire s1t_snan_b = s1t_expb_ff & !s1t_fractb[22] & (|s1t_fractb[21:0]);
  wire s1t_qnan_b = s1t_expb_ff &  s1t_fractb[22];
    // opa or opb is denormalized
  wire s1t_opa_dn = !(|s1t_expa);
  wire s1t_opb_dn = !(|s1t_expb);

  wire s1t_expa_gt_expb = (s1t_expa > s1t_expb);

    // convert to an easy to handle floating-point format
  wire [FRAC_WIDTH+4 : 0] s1t_fracta_28, s1t_fractb_28,
                          s1t_fract_sm_28;

  assign s1t_fracta_28 = s1t_opa_dn ?
    {2'b00, s1t_fracta, 3'b000} : {2'b01, s1t_fracta, 3'b000};
  assign s1t_fractb_28 = s1t_opb_dn ?
    {2'b00, s1t_fractb, 3'b000} : {2'b01, s1t_fractb, 3'b000};

  assign s1t_fract_sm_28 =  s1t_expa_gt_expb ? s1t_fractb_28 : s1t_fracta_28;

  // stage #1 outputs
  wire [1:0] s1t_mux_diff = {s1t_expa_gt_expb, s1t_opa_dn ^ s1t_opb_dn};
  
  reg [EXP_WIDTH-1 : 0]  s1o_exp;
  reg [EXP_WIDTH-1 : 0]  s1o_exp_diff;
  reg                    s1o_expa_gt_expb;
  reg [FRAC_WIDTH+4 : 0] s1o_fract_sm_28, s1o_fracta_28, s1o_fractb_28;
  reg [5:0]              s1o_rzeros;
  reg                    s1o_signa, s1o_signb, s1o_infa, s1o_infb,
                         s1o_snan_a, s1o_qnan_a, s1o_snan_b, s1o_qnan_b;

  reg s1o_is_sub;

  always @(posedge clk) begin
    if(adv_i) begin
      s1o_exp <= s1t_expa_gt_expb ? s1t_expa : s1t_expb;
        // calculate howmany postions the fraction will be shifted 
      case(s1t_mux_diff) // synopsys full_case parallel_case
        2'b00: s1o_exp_diff <= s1t_expb - s1t_expa;
        2'b01: s1o_exp_diff <= s1t_expb - (s1t_expa + 8'd1);
        2'b10: s1o_exp_diff <= s1t_expa - s1t_expb;
        2'b11: s1o_exp_diff <= s1t_expa - (s1t_expb + 8'd1);
      endcase
        //
      s1o_expa_gt_expb <= s1t_expa_gt_expb;
        // fractionlas
      s1o_fract_sm_28 <= s1t_fract_sm_28;
      s1o_fracta_28   <= s1t_fracta_28;
      s1o_fractb_28   <= s1t_fractb_28;
        // count the zeros from right to check if result is inexact
      casez(s1t_fract_sm_28) // synopsys full_case parallel_case
        28'b???????????????????????????1: s1o_rzeros <= 0;
        28'b??????????????????????????10: s1o_rzeros <= 1;
        28'b?????????????????????????100: s1o_rzeros <= 2;
        28'b????????????????????????1000: s1o_rzeros <= 3;
        28'b???????????????????????10000: s1o_rzeros <= 4;
        28'b??????????????????????100000: s1o_rzeros <= 5;
        28'b?????????????????????1000000: s1o_rzeros <= 6;
        28'b????????????????????10000000: s1o_rzeros <= 7;
        28'b???????????????????100000000: s1o_rzeros <= 8;
        28'b??????????????????1000000000: s1o_rzeros <= 9;
        28'b?????????????????10000000000: s1o_rzeros <= 10;
        28'b????????????????100000000000: s1o_rzeros <= 11;
        28'b???????????????1000000000000: s1o_rzeros <= 12;
        28'b??????????????10000000000000: s1o_rzeros <= 13;
        28'b?????????????100000000000000: s1o_rzeros <= 14;
        28'b????????????1000000000000000: s1o_rzeros <= 15;
        28'b???????????10000000000000000: s1o_rzeros <= 16;
        28'b??????????100000000000000000: s1o_rzeros <= 17;
        28'b?????????1000000000000000000: s1o_rzeros <= 18;
        28'b????????10000000000000000000: s1o_rzeros <= 19;
        28'b???????100000000000000000000: s1o_rzeros <= 20;
        28'b??????1000000000000000000000: s1o_rzeros <= 21;
        28'b?????10000000000000000000000: s1o_rzeros <= 22;
        28'b????100000000000000000000000: s1o_rzeros <= 23;
        28'b???1000000000000000000000000: s1o_rzeros <= 24;
        28'b??10000000000000000000000000: s1o_rzeros <= 25;
        28'b?100000000000000000000000000: s1o_rzeros <= 26;
        28'b1000000000000000000000000000: s1o_rzeros <= 27;
        28'b0000000000000000000000000000: s1o_rzeros <= 28;
      endcase // casex (fract_sm_28)
        // input related
      s1o_signa <= s1t_signa;
      s1o_signb <= s1t_signb;
      s1o_infa  <= s1t_infa;
      s1o_infb  <= s1t_infb;
      s1o_snan_a <= s1t_snan_a;
      s1o_qnan_a <= s1t_qnan_a;
      s1o_snan_b <= s1t_snan_b;
      s1o_qnan_b <= s1t_qnan_b;
        // controls and states
      s1o_is_sub <= is_sub_i;
    end // advance
  end // posedge clock

  // ready is special case
  reg s1o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      s1o_ready  <= 0;
    else if(adv_i)
      s1o_ready <= start_i;
  end // posedge clock


  /* Stage #2 */

  // shift-right the fraction if necessary
  wire [FRAC_WIDTH+4 : 0] s2t_fract_shr_28 ;  
  assign s2t_fract_shr_28 = s1o_fract_sm_28 >> s1o_exp_diff;

  wire s2t_sticky = (s1o_exp_diff > {2'b00,s1o_rzeros}) & (|s1o_fract_sm_28);

  wire [FRAC_WIDTH+4 : 0] s2t_fracta_28, s2t_fractb_28;

  assign s2t_fracta_28 = s1o_expa_gt_expb ?
    s1o_fracta_28 :
    {s2t_fract_shr_28[27:1],(s2t_sticky|s2t_fract_shr_28[0])};

  assign s2t_fractb_28 =  s1o_expa_gt_expb ?
     {s2t_fract_shr_28[27:1],(s2t_sticky|s2t_fract_shr_28[0])} :
     s1o_fractb_28;

  // stage #2 outputs
  reg [FRAC_WIDTH+4:0] s2o_fracta_28;
  reg [FRAC_WIDTH+4:0] s2o_fractb_28;
  reg [EXP_WIDTH-1:0]  s2o_exp;
  reg                  s2o_signa, s2o_signb, s2o_infa, s2o_infb,
                       s2o_snan_a, s2o_qnan_a, s2o_snan_b, s2o_qnan_b;  

  reg s2o_is_sub;

  always @(posedge clk) begin
    if(adv_i) begin
      s2o_exp <= s1o_exp;
      s2o_fracta_28 <= s2t_fracta_28;
      s2o_fractb_28 <= s2t_fractb_28;
      s2o_signa <= s1o_signa;
      s2o_signb <= s1o_signb;
      s2o_infa  <= s1o_infa;
      s2o_infb  <= s1o_infb;
      s2o_snan_a <= s1o_snan_a;
      s2o_qnan_a <= s1o_qnan_a;
      s2o_snan_b <= s1o_snan_b;
      s2o_qnan_b <= s1o_qnan_b;
      s2o_is_sub <= s1o_is_sub;
    end // advance
  end // posedge clock

  // ready is special case
  reg s2o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      s2o_ready  <= 0;
    else if(adv_i)
      s2o_ready <= s1o_ready;
  end // posedge clock

  
  /*
    Stage #3
    addition / substruction
  */

  wire s3t_fracta_gt_fractb = s2o_fracta_28 > s2o_fractb_28;

   // check if its a subtraction or an addition operation
  wire s3t_addop = ((s2o_signa ^ s2o_signb) & !s2o_is_sub) |
                   ((s2o_signa ^ (~s2o_signb)) & s2o_is_sub);

   // add/substract
  wire [FRAC_WIDTH+4:0] s3t_fract28;
  assign s3t_fract28 = s3t_addop ?
    (s3t_fracta_gt_fractb ? (s2o_fracta_28 - s2o_fractb_28) :
                            (s2o_fractb_28 - s2o_fracta_28)) :
                            (s2o_fracta_28 + s2o_fractb_28);

   // sign of result
  wire s3t_sign = ((s3t_fract28 == 28'd0) & !(s2o_signa & s2o_signb)) ? 0 :
        ( (!s2o_signa & (!s3t_fracta_gt_fractb & (s2o_is_sub^s2o_signb)))|
         (s2o_signa & (s3t_fracta_gt_fractb | (s2o_is_sub^s2o_signb))) );

   // stage #3 outputs
  reg s3o_sign;
  reg [EXP_WIDTH-1:0]  s3o_exp;
  reg [FRAC_WIDTH+4:0] s3o_fract28;
  reg                  s3o_signa, s3o_signb, s3o_infa, s3o_infb,
                       s3o_snan_a, s3o_qnan_a, s3o_snan_b, s3o_qnan_b;

  reg s3o_is_sub;
  
  always @(posedge clk) begin
    if(adv_i) begin
      s3o_exp <= s2o_exp;
      s3o_fract28 <= s3t_fract28;
      s3o_sign <= s3t_sign;
      s3o_signa <= s2o_signa;
      s3o_signb <= s2o_signb;
      s3o_infa <= s2o_infa;
      s3o_infb <= s2o_infb;
      s3o_snan_a <= s2o_snan_a;
      s3o_qnan_a <= s2o_qnan_a;
      s3o_snan_b <= s2o_snan_b;
      s3o_qnan_b <= s2o_qnan_b;
      s3o_is_sub <= s2o_is_sub;
    end // advance
  end // posedge clock

  // ready is special case
  reg s3o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      s3o_ready  <= 0;
    else if(adv_i)
      s3o_ready <= s2o_ready;
  end // posedge clock

  
  /*
    Stages #4, #5 and #6
    post addition / substruction normalization
  */

  /* Stage #4 */
  // figure out the output exponent and how much the fraction has to be
  // shiftd right/left

  reg [5:0] s4t_lzeroes;
  always @(s3o_fract28)
    casez(s3o_fract28[26:0])  // synopsys full_case parallel_case
      27'b1??????????????????????????: s4t_lzeroes = 0;
      27'b01?????????????????????????: s4t_lzeroes = 1;
      27'b001????????????????????????: s4t_lzeroes = 2;
      27'b0001???????????????????????: s4t_lzeroes = 3;
      27'b00001??????????????????????: s4t_lzeroes = 4;
      27'b000001?????????????????????: s4t_lzeroes = 5;
      27'b0000001????????????????????: s4t_lzeroes = 6;
      27'b00000001???????????????????: s4t_lzeroes = 7;
      27'b000000001??????????????????: s4t_lzeroes = 8;
      27'b0000000001?????????????????: s4t_lzeroes = 9;
      27'b00000000001????????????????: s4t_lzeroes = 10;
      27'b000000000001???????????????: s4t_lzeroes = 11;
      27'b0000000000001??????????????: s4t_lzeroes = 12;
      27'b00000000000001?????????????: s4t_lzeroes = 13;
      27'b000000000000001????????????: s4t_lzeroes = 14;
      27'b0000000000000001???????????: s4t_lzeroes = 15;
      27'b00000000000000001??????????: s4t_lzeroes = 16;
      27'b000000000000000001?????????: s4t_lzeroes = 17;
      27'b0000000000000000001????????: s4t_lzeroes = 18;
      27'b00000000000000000001???????: s4t_lzeroes = 19;
      27'b000000000000000000001??????: s4t_lzeroes = 20;
      27'b0000000000000000000001?????: s4t_lzeroes = 21;
      27'b00000000000000000000001????: s4t_lzeroes = 22;
      27'b000000000000000000000001???: s4t_lzeroes = 23;
      27'b0000000000000000000000001??: s4t_lzeroes = 24;
      27'b00000000000000000000000001?: s4t_lzeroes = 25;
      27'b000000000000000000000000001: s4t_lzeroes = 26;
      27'b000000000000000000000000000: s4t_lzeroes = 27;
    endcase

  wire s4t_carry = s3o_fract28[27];

  wire [5:0] s4t_zeros = s4t_carry ? 0 : s4t_lzeroes;

  // negative flag & large flag & exp
  wire [9:0] s4t_exp10 = {2'd0,s3o_exp} + {9'd0,s4t_carry} - {4'd0,s4t_zeros};

  // stage #4 outputs
  reg [5:0] s4o_shr;
  reg [5:0] s4o_shl;
  reg [EXP_WIDTH:0] s4o_exp9;
  reg [FRAC_WIDTH+4:0] s4o_fract28;
  reg s4o_zero_fract;
  reg s4o_sign;
  reg s4o_signa, s4o_signb, s4o_infa, s4o_infb,
      s4o_snan_a, s4o_qnan_a, s4o_snan_b, s4o_qnan_b;

  reg s4o_is_sub;
  
  always @(posedge clk) begin
    if(adv_i) begin    
      if (s4t_exp10[9] | !(|s4t_exp10)) begin
        s4o_shr <= 0;
        s4o_exp9 <= 9'd1;

        if (|s3o_exp)
          s4o_shl <= s3o_exp[5:0] - 6'd1;
        else
          s4o_shl <= 0;
      end
      else if (s4t_exp10[8]) begin
        s4o_shr <= 0;
        s4o_shl <= 0;
        s4o_exp9 <= 9'b011111111;
      end
      else begin
        s4o_shr <= {5'd0,s4t_carry};
        s4o_shl <= s4t_zeros;
        s4o_exp9 <= s4t_exp10[8:0];
      end
        // output related
      s4o_sign  <= s3o_sign;
      s4o_fract28 <= s3o_fract28;
      s4o_zero_fract <= (s4t_zeros == 27);
        // input related
      s4o_signa <= s3o_signa;
      s4o_signb <= s3o_signb;
      s4o_infa  <= s3o_infa;
      s4o_infb  <= s3o_infb;
      s4o_snan_a <= s3o_snan_a;
      s4o_qnan_a <= s3o_qnan_a;
      s4o_snan_b <= s3o_snan_b;
      s4o_qnan_b <= s3o_qnan_b;
        // controls
      s4o_is_sub <= s3o_is_sub;
    end // advance
  end // posedge clock

  // ready is special case
  reg s4o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      s4o_ready  <= 0;
    else if(adv_i)
      s4o_ready <= s3o_ready;
  end // posedge clock


  /* Stage #5 */
  
    // Shifting the fraction
  reg [EXP_WIDTH:0] s5o_exp9;
  reg [FRAC_WIDTH+4:0] s5o_fract28;
  reg s5o_zero_fract;
  reg s5o_sticky;
  reg s5o_lost;
  reg s5o_sign;
  reg s5o_signa, s5o_signb, s5o_infa, s5o_infb,
      s5o_snan_a, s5o_qnan_a, s5o_snan_b, s5o_qnan_b;

  reg s5o_is_sub;

  always @(posedge clk) begin
    if(adv_i) begin
        // exponents
      s5o_exp9 <= s4o_exp9;
        // fractionals
      s5o_zero_fract <= s4o_zero_fract;      
      s5o_sticky <= (s4o_fract28[0] & s4o_fract28[27]);
      s5o_lost <= (s4o_shr[0] & s4o_fract28[0]);
      if (|s4o_shr)
        s5o_fract28 <= s4o_fract28 >> s4o_shr;
      else
        s5o_fract28 <= s4o_fract28 << s4o_shl;
        // output related
      s5o_sign  <= s4o_sign;
        // input related
      s5o_signa <= s4o_signa;
      s5o_signb <= s4o_signb;
      s5o_infa  <= s4o_infa;
      s5o_infb  <= s4o_infb;
      s5o_snan_a <= s4o_snan_a;
      s5o_qnan_a <= s4o_qnan_a;
      s5o_snan_b <= s4o_snan_b;
      s5o_qnan_b <= s4o_qnan_b;
        // controls
      s5o_is_sub <= s4o_is_sub;
    end // (reset or flush) / advance
  end // posedge clock

  // ready is special case
  reg s5o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      s5o_ready  <= 0;
    else if(adv_i)
      s5o_ready <= s4o_ready;
  end // posedge clock

  /* Stage #6 - round */
  wire [EXP_WIDTH:0] s6t_exp9;
  assign s6t_exp9 = (s5o_fract28[27:26]==2'b00) ?
                    (s5o_exp9 - 9'd1) : s5o_exp9;

  //check last bit, before and after right-shift
  wire s6t_sticky = s5o_fract28[0] | s5o_sticky;

  wire s6t_roundup =
    // round to nearset even
    (rmode_i==2'b00) ?
      (s5o_fract28[2] & ((s5o_fract28[1] | s6t_sticky) | s5o_fract28[3])) :
    // round up
    (rmode_i==2'b10) ?
      ((s5o_fract28[2] | s5o_fract28[1] | s6t_sticky) & !s5o_sign):
    // round down
    (rmode_i==2'b11) ?
      ((s5o_fract28[2] | s5o_fract28[1] | s6t_sticky) & s5o_sign) :
    // round to zero(truncate = no rounding)
      0;

  wire [FRAC_WIDTH+4:0] s6t_fract28_rnd;
  assign s6t_fract28_rnd = s6t_roundup ?
         s5o_fract28+28'b0000_0000_0000_0000_0000_0000_1000 :
         s5o_fract28;

  // right-shift after rounding (if necessary)
  wire s6t_shr = s6t_fract28_rnd[27];

  wire [EXP_WIDTH:0] s6t_exp9_rnd;
  assign s6t_exp9_rnd = (s6t_shr & (s6t_exp9!=9'b011111111)) ?
                        (s6t_exp9 + 9'b000000001) : s6t_exp9;

  wire [FRAC_WIDTH+4:0] s6t_fract28;
  assign s6t_fract28 = s6t_shr ? {1'b0,s6t_fract28_rnd[27:1]} : s6t_fract28_rnd;

  // input nans
  wire s6t_anan_a  = s5o_snan_a | s5o_qnan_a;
  wire s6t_anan_b  = s5o_snan_b | s5o_qnan_b;
  wire s6t_snan_in = s5o_snan_a | s5o_snan_b;
  wire s6t_anan_in = s6t_anan_a | s6t_anan_b;

  // "infs" (actually exp==8'hff)
  wire s6t_expa_ff = s6t_anan_a | s5o_infa;
  wire s6t_expb_ff = s6t_anan_b | s5o_infb;

  // inf-inf=Nan
  wire s6t_inv = ((s6t_expa_ff & s6t_expb_ff) &
                  (s5o_signa ^ (s5o_is_sub ^ s5o_signb))) |
                  s6t_snan_in;

  wire s6t_opc_nan = s6t_anan_in | s6t_inv;

  wire s6t_nan_sign =
     (s6t_anan_a & s6t_anan_b) ? s5o_sign :
      s6t_anan_a ? s5o_signa : s5o_signb;

  // check if result is inexact;
  wire s6t_lost = s5o_lost |
       (s6t_shr & s6t_fract28_rnd[0]) | (|s6t_fract28[2:0]);

  wire s6t_ovf = (s6t_exp9_rnd==9'b011111111) & !(s6t_expa_ff | s6t_expb_ff);
  wire s6t_ine = (s6t_lost | s6t_ovf) & !(s6t_expa_ff | s6t_expb_ff);

   // Generate result   
  wire [31:0] s6t_opc;
  assign s6t_opc =
    s6t_opc_nan ? {s6t_nan_sign,QNAN} :
    (s6t_expa_ff | s6t_expb_ff | s6t_ovf) ? {s5o_sign,INF} :
    s5o_zero_fract ? {s5o_sign,31'd0} :
    {s5o_sign,s6t_exp9_rnd[7:0],s6t_fract28[25:3]};

   // Output Register
  always @(posedge clk) begin
    if(adv_i) begin
      opc_o   <= s6t_opc;
      ine_o   <= s6t_ine;
      inv_o   <= s6t_inv;
      ovf_o   <= (&s6t_opc[30:23]) & s6t_ine;
      inf_o   <= (&s6t_opc[30:23]) & !s6t_opc_nan;
      unf_o   <= (!(|s6t_opc[30:0])) & s6t_ine;
      zer_o   <= !(|s6t_opc[30:0]);  
    end
  end // posedge clock

  // ready is special case
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      ready_o <= 0;
    else if(adv_i)
      ready_o <= s5o_ready;
  end // posedge clock

endmodule // pfpu32_addsub


