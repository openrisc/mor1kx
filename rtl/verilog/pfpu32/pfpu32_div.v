//////////////////////////////////////////////////////////////////////
//                                                                  //
//    pfpu32_div                                                    //
//                                                                  //
//    This file is part of the mor1kx project                       //
//    https://github.com/openrisc/mor1kx                            //
//                                                                  //
//    Description                                                   //
//    divider pipeline for single precision floating                //
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

//`define NEW_F32_DIV

module pfpu32_div
(
   input             clk,
   input             rst,
   input             flush_i,  // flushe pipe
   input             adv_i,    // advance pipe
   input             start_i,  // start division
   input       [1:0] rmode_i,  // round mode
   input      [31:0] opa_i,
   input      [31:0] opb_i,
   output reg [31:0] opc_o,
   output reg        ine_o,
   output reg        inv_o,    // 0/0, inf/inf -> invalid flag & qnan result
   output reg        ovf_o,
   output reg        inf_o,
   output reg        unf_o,
   output reg        zer_o,    // zero rezult
   output reg        dbz_o,    // division by zero
   output reg        ready_o
);

  localparam INF  = 31'b1111111100000000000000000000000;
  localparam QNAN = 31'b1111111110000000000000000000000;

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


  /* Stage #1: pre-division normalization */

    // aliases
  wire s1t_signa = opa_i[31];
  wire s1t_signb = opb_i[31];
  wire [7:0]  s1t_expa = opa_i[30:23];
  wire [7:0]  s1t_expb = opb_i[30:23];
  wire [22:0] s1t_fracta = opa_i[22:0];
  wire [22:0] s1t_fractb = opb_i[22:0];

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
    // opa or opb is zero
  wire s1t_opa_0 = !(|opa_i[30:0]);
  wire s1t_opb_0 = !(|opb_i[30:0]);
    // opa or opb is denormalized
  wire s1t_opa_dn = !(|s1t_expa) & !s1t_opa_0;
  wire s1t_opb_dn = !(|s1t_expb) & !s1t_opb_0;

    // restored fractionals
  wire [23:0] s1t_fract24a = {(!s1t_opa_dn & !s1t_opa_0),s1t_fracta};
  wire [23:0] s1t_fract24b = {(!s1t_opb_dn & !s1t_opb_0),s1t_fractb};

  // count leading zeros
  reg [5:0] s1t_dvd_zeros;
  always @(s1t_fract24a)
    casez(s1t_fract24a) // synopsys full_case parallel_case
      24'b1???????????????????????: s1t_dvd_zeros =  0;
      24'b01??????????????????????: s1t_dvd_zeros =  1;
      24'b001?????????????????????: s1t_dvd_zeros =  2;
      24'b0001????????????????????: s1t_dvd_zeros =  3;
      24'b00001???????????????????: s1t_dvd_zeros =  4;
      24'b000001??????????????????: s1t_dvd_zeros =  5;
      24'b0000001?????????????????: s1t_dvd_zeros =  6;
      24'b00000001????????????????: s1t_dvd_zeros =  7;
      24'b000000001???????????????: s1t_dvd_zeros =  8;
      24'b0000000001??????????????: s1t_dvd_zeros =  9;
      24'b00000000001?????????????: s1t_dvd_zeros = 10;
      24'b000000000001????????????: s1t_dvd_zeros = 11;
      24'b0000000000001???????????: s1t_dvd_zeros = 12;
      24'b00000000000001??????????: s1t_dvd_zeros = 13;
      24'b000000000000001?????????: s1t_dvd_zeros = 14;
      24'b0000000000000001????????: s1t_dvd_zeros = 15;
      24'b00000000000000001???????: s1t_dvd_zeros = 16;
      24'b000000000000000001??????: s1t_dvd_zeros = 17;
      24'b0000000000000000001?????: s1t_dvd_zeros = 18;
      24'b00000000000000000001????: s1t_dvd_zeros = 19;
      24'b000000000000000000001???: s1t_dvd_zeros = 20;
      24'b0000000000000000000001??: s1t_dvd_zeros = 21;
      24'b00000000000000000000001?: s1t_dvd_zeros = 22;
      24'b000000000000000000000001: s1t_dvd_zeros = 23;
      24'b000000000000000000000000: s1t_dvd_zeros =  0; // zero rezult
    endcase

  // count leading zeros
  reg [5:0] s1t_div_zeros;
  always @(s1t_fract24b)
    casez(s1t_fract24b) // synopsys full_case parallel_case
      24'b1???????????????????????: s1t_div_zeros =  0;
      24'b01??????????????????????: s1t_div_zeros =  1;
      24'b001?????????????????????: s1t_div_zeros =  2;
      24'b0001????????????????????: s1t_div_zeros =  3;
      24'b00001???????????????????: s1t_div_zeros =  4;
      24'b000001??????????????????: s1t_div_zeros =  5;
      24'b0000001?????????????????: s1t_div_zeros =  6;
      24'b00000001????????????????: s1t_div_zeros =  7;
      24'b000000001???????????????: s1t_div_zeros =  8;
      24'b0000000001??????????????: s1t_div_zeros =  9;
      24'b00000000001?????????????: s1t_div_zeros = 10;
      24'b000000000001????????????: s1t_div_zeros = 11;
      24'b0000000000001???????????: s1t_div_zeros = 12;
      24'b00000000000001??????????: s1t_div_zeros = 13;
      24'b000000000000001?????????: s1t_div_zeros = 14;
      24'b0000000000000001????????: s1t_div_zeros = 15;
      24'b00000000000000001???????: s1t_div_zeros = 16;
      24'b000000000000000001??????: s1t_div_zeros = 17;
      24'b0000000000000000001?????: s1t_div_zeros = 18;
      24'b00000000000000000001????: s1t_div_zeros = 19;
      24'b000000000000000000001???: s1t_div_zeros = 20;
      24'b0000000000000000000001??: s1t_div_zeros = 21;
      24'b00000000000000000000001?: s1t_div_zeros = 22;
      24'b000000000000000000000001: s1t_div_zeros = 23;
      24'b000000000000000000000000: s1t_div_zeros =  0; // zero result
    endcase

  // left-shift the dividend and divisor
  wire [23:0] s1t_fracta_lshift_intermediate;
  wire [23:0] s1t_fractb_lshift_intermediate;
  assign s1t_fracta_lshift_intermediate = s1t_fract24a << s1t_dvd_zeros;
  assign s1t_fractb_lshift_intermediate = s1t_fract24b << s1t_div_zeros;

  wire [9:0] s1t_expa_10 = {2'd0,s1t_expa} + {9'd0,s1t_opa_dn};
  wire [9:0] s1t_expb_10 = {2'd0,s1t_expb} + {9'd0,s1t_opb_dn};

  // stage #1 outputs
  //   input related
  reg s1o_infa, s1o_infb,
      s1o_snan_a, s1o_qnan_a, s1o_snan_b, s1o_qnan_b;
  reg s1o_opa_0, s1o_opb_0;
  //   computation related
  reg s1o_sign;
  reg [9:0]  s1o_exp10;
  reg [49:0] s1o_dvdnd_50;
  reg [26:0] s1o_dvsor_27;

  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s1o_infa   <= s1t_infa;
      s1o_infb   <= s1t_infb;
      s1o_snan_a <= s1t_snan_a;
      s1o_qnan_a <= s1t_qnan_a;
      s1o_snan_b <= s1t_snan_b;
      s1o_qnan_b <= s1t_qnan_b;
      s1o_opa_0  <= s1t_opa_0;
      s1o_opb_0  <= s1t_opb_0;
        // computation related
      s1o_sign     <= s1t_signa ^ s1t_signb;
      s1o_exp10    <= (s1t_expa_10 - s1t_expb_10 + 10'd127 -
                       {4'd0,s1t_dvd_zeros} + {4'd0,s1t_div_zeros})
                      & {10{!(s1t_opa_0 | s1t_opb_0)}};
      s1o_dvdnd_50 <= {s1t_fracta_lshift_intermediate,26'd0};
      s1o_dvsor_27 <= {3'd0,s1t_fractb_lshift_intermediate};
    end // advance
  end // posedge clock

  // ready is special case
  reg s1o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      s1o_ready <= 0;
    else if(adv_i)
      s1o_ready <= start_i;
  end // posedge clock


  /* Stage #2: division */

  localparam STATE_WAITING = 1'b0,
             STATE_BUSY    = 1'b1;

  reg       s2t_ready;
  reg       s2t_state;
  reg [4:0] s2t_count;

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i) begin
      s2t_state <= STATE_WAITING;
      s2t_ready <= 1'b0;
    end
    else if (s1o_ready & adv_i) begin
      s2t_state <= STATE_BUSY;
      s2t_count <= 5'd26;
    end
    else if ((!(|s2t_count) & s2t_state==STATE_BUSY) & adv_i) begin
      s2t_state <= STATE_WAITING;
      s2t_ready <= 1'b1;
      s2t_count <= 5'd26;
    end
    else if ((s2t_state==STATE_BUSY) & adv_i)
      s2t_count <= s2t_count - 5'd1;
    else if(adv_i) begin
      s2t_state <= STATE_WAITING;
      s2t_ready <= 1'b0;
    end
  end // posedge clock

  reg  [26:0] s2t_qutnt;
  reg  [26:0] s2t_rmndr;
  reg  [26:0] s2t_dvd;

  wire [26:0] v2t_div;
  wire [26:0] v2t_div_minus_s1o_dvsor_27;

  assign v2t_div = (s2t_count==5'd26) ? {3'd0,s1o_dvdnd_50[49:26]} : s2t_dvd;
  assign v2t_div_minus_s1o_dvsor_27 = v2t_div - s1o_dvsor_27;

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i) begin
      s2t_qutnt <= 1'b0;
      s2t_rmndr <= 1'b0;
    end
    else if (s1o_ready & adv_i) begin
      s2t_qutnt <= 1'b0;
      s2t_rmndr <= 1'b0;
    end
    else if ((s2t_state==STATE_BUSY) & adv_i) begin
      if (v2t_div < s1o_dvsor_27) begin
        s2t_qutnt[s2t_count] <= 1'b0;
        s2t_dvd <= {v2t_div[25:0],1'b0};
      end
      else begin
        s2t_qutnt[s2t_count] <= 1'b1;
        s2t_dvd <= {v2t_div_minus_s1o_dvsor_27[25:0],1'b0};
      end

      s2t_rmndr <= v2t_div;
    end // if (s2t_state==STATE_BUSY)
  end // posedge

  // stage #2 outputs
  //   input related
  reg s2o_infa, s2o_infb,
      s2o_snan_a, s2o_qnan_a, s2o_snan_b, s2o_qnan_b;
  reg s2o_opa_0, s2o_opb_0;
  //   computation related
  reg        s2o_sign;
  reg [9:0]  s2o_exp10;
  reg [25:0] s2o_qutnt;

  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s2o_infa   <= s1o_infa;
      s2o_infb   <= s1o_infb;
      s2o_snan_a <= s1o_snan_a;
      s2o_qnan_a <= s1o_qnan_a;
      s2o_snan_b <= s1o_snan_b;
      s2o_qnan_b <= s1o_qnan_b;
      s2o_opa_0  <= s1o_opa_0;
      s2o_opb_0  <= s1o_opb_0;
        // computation related
      s2o_sign  <= s1o_sign;
      s2o_exp10 <= s1o_exp10;
      s2o_qutnt <= {s2t_qutnt[26:2],((|s2t_qutnt[1:0]) | (|s2t_rmndr))};
    end // (reset or flush) / advance
  end // posedge clock

  // ready is special case
  reg s2o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      s2o_ready <= 0;
    else if(adv_i)
      s2o_ready <= s2t_ready;
  end // posedge clock


  /* Stage #3: calc align values */  

  // qutnt
  // 25 24                    2
  // |  |                     |
  // h  fffffffffffffffffffffff rs

  wire s3t_opc_0 = s2o_opa_0 | s2o_opb_0; // secially fo here

  // rigt shift value
  // and appropriatelly corrected exponent
  wire s2o_exp10_0 = !(|s2o_exp10);
  wire [9:0] s3t_shr_of_neg_exp = 11'h401 - {1'b0,s2o_exp10}; // 1024-v+1
  //...
  wire [9:0] s3t_shrx;
  wire [9:0] s3t_exp10rx;
  assign {s3t_shrx,s3t_exp10rx} =
      // zero result case
    s3t_opc_0    ? {10'd0,10'd0} :
      // negative exponent sum
      //  (!) takes carry into account automatically
    s2o_exp10[9] ? {s3t_shr_of_neg_exp,10'd1} :
      // zero exponent sum (denorm. result potentially)
    (!s3t_opc_0 & s2o_exp10_0) ? 
                    {10'd1,10'd1} :
      // normal case at last
                    {10'd0,s2o_exp10};
  // max. right shift that makes sense is 25bits
  //  i.e. [25] moves to sticky position: ([0])
  wire [5:0] s3t_shr = (s3t_shrx > 10'd25) ? 6'd25 : s3t_shrx[5:0];

  // in fact, as the dividend and divisor was normalized
  // and the result is non-zero
  // the '1' is maximum number of leading zeros in the quotient
  wire s3t_nlz = !s2o_qutnt[25];
    //...
  wire [9:0] s3t_exp10_m1 = s2o_exp10 - 10'd1;
  // left shift flag and corrected exponent
  wire       s3t_shlx;
  wire [9:0] s3t_exp10lx;
  assign {s3t_shlx,s3t_exp10lx} =
      // shift isn't needed (includes zero result)
    (!s3t_nlz)           ? {1'b0,s2o_exp10} :
      // normalization is possible
    (s2o_exp10 >  10'd1) ? {1'b1,s3t_exp10_m1} :
      // denormalized cases
                           {1'b0,10'd1};

  // align
  wire [25:0] s3t_fract26 =
    (|s3t_shr) ? (s2o_qutnt >> s3t_shr) :
                 (s2o_qutnt << s3t_shlx);

  // sticky bit computation for right shift
  // max. right shift that makes sense i 25bits
  //  i.e. [25] moves to sticky position: ([0])
  reg s3t_sticky_shr;
  always @(s3t_shr or s2o_qutnt) begin
    case(s3t_shr)
      6'd0   : s3t_sticky_shr =  s2o_qutnt[   0];
      6'd1   : s3t_sticky_shr = |s2o_qutnt[ 1:0];
      6'd2   : s3t_sticky_shr = |s2o_qutnt[ 2:0];
      6'd3   : s3t_sticky_shr = |s2o_qutnt[ 3:0];
      6'd4   : s3t_sticky_shr = |s2o_qutnt[ 4:0];
      6'd5   : s3t_sticky_shr = |s2o_qutnt[ 5:0];
      6'd6   : s3t_sticky_shr = |s2o_qutnt[ 6:0];
      6'd7   : s3t_sticky_shr = |s2o_qutnt[ 7:0];
      6'd8   : s3t_sticky_shr = |s2o_qutnt[ 8:0];
      6'd9   : s3t_sticky_shr = |s2o_qutnt[ 9:0];
      6'd10  : s3t_sticky_shr = |s2o_qutnt[10:0];
      6'd11  : s3t_sticky_shr = |s2o_qutnt[11:0];
      6'd12  : s3t_sticky_shr = |s2o_qutnt[12:0];
      6'd13  : s3t_sticky_shr = |s2o_qutnt[13:0];
      6'd14  : s3t_sticky_shr = |s2o_qutnt[14:0];
      6'd15  : s3t_sticky_shr = |s2o_qutnt[15:0];
      6'd16  : s3t_sticky_shr = |s2o_qutnt[16:0];
      6'd17  : s3t_sticky_shr = |s2o_qutnt[17:0];
      6'd18  : s3t_sticky_shr = |s2o_qutnt[18:0];
      6'd19  : s3t_sticky_shr = |s2o_qutnt[19:0];
      6'd20  : s3t_sticky_shr = |s2o_qutnt[20:0];
      6'd21  : s3t_sticky_shr = |s2o_qutnt[21:0];
      6'd22  : s3t_sticky_shr = |s2o_qutnt[22:0];
      6'd23  : s3t_sticky_shr = |s2o_qutnt[23:0];
      6'd24  : s3t_sticky_shr = |s2o_qutnt[24:0];
      default: s3t_sticky_shr = |s2o_qutnt[25:0];
    endcase
  end // always

  wire s3t_sticky = (|s3t_shr) ? s3t_sticky_shr : s3t_fract26[0];

   // stage #3 outputs
    // input related
  reg  s3o_signa, s3o_signb, s3o_infa, s3o_infb,
       s3o_snan_a, s3o_qnan_a, s3o_snan_b, s3o_qnan_b;
  reg  s3o_opa_0, s3o_opb_0;
      // computation related
  reg        s3o_signc;
  reg [9:0]  s3o_exp10c;
  reg [25:0] s3o_fract26c;
  
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s3o_infa   <= s2o_infa;
      s3o_infb   <= s2o_infb;
      s3o_snan_a <= s2o_snan_a;
      s3o_qnan_a <= s2o_qnan_a;
      s3o_snan_b <= s2o_snan_b;
      s3o_qnan_b <= s2o_qnan_b;
      s3o_opa_0  <= s2o_opa_0;
      s3o_opb_0  <= s2o_opb_0;
        // computation related
      s3o_signc    <= s2o_sign;
      s3o_exp10c   <= (|s3t_shr) ? s3t_exp10rx : s3t_exp10lx;
      s3o_fract26c <= {s3t_fract26[25:1],s3t_sticky};
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


  /* Stage #4: rounding and output */
  
  wire s4t_g    = s3o_fract26c[2];
  wire s4t_r    = s3o_fract26c[1];
  wire s4t_s    = s3o_fract26c[0];
  wire s4t_lost = s4t_r | s4t_s;

  wire s4t_rnd_up = (rm_nearest & s4t_r & s4t_s) |
                    (rm_nearest & s4t_g & s4t_r & !s4t_s) |
                    (rm_to_infp & !s3o_signc & s4t_lost) |
                    (rm_to_infm &  s3o_signc & s4t_lost);

  wire [24:0] s4t_fract25c = s4t_rnd_up ?
    ({1'b0,s3o_fract26c[25:2]} + 25'd1) :
     {1'b0,s3o_fract26c[25:2]};

  wire s4t_shr = s4t_fract25c[24];

  wire [9:0]  s4t_exp10c   = s3o_exp10c + {9'd0,s4t_shr};
  wire [23:0] s4t_fract24c = s4t_shr ? s4t_fract25c[24:1] :
                                       s4t_fract25c[23:0];

  wire s4t_fract24c_dn = !s4t_fract24c[23];
  wire s4t_fract24c_00 = !(|s4t_fract24c);

  // input nans
  wire s4t_anan_a  = s3o_snan_a | s3o_qnan_a;
  wire s4t_anan_b  = s3o_snan_b | s3o_qnan_b;
  wire s4t_snan_in = s3o_snan_a | s3o_snan_b;
  wire s4t_anan_in = s4t_anan_a | s4t_anan_b;

  //  0/0, inf/inf -> invalid flag, qnan result
  wire s4t_inv = (s3o_opa_0 & s3o_opb_0) | 
                 (s3o_infa & s3o_infb)   | 
                 s4t_snan_in;

  wire s4t_opc_nan  = s4t_anan_in | s4t_inv;
  wire s4t_nan_sign = s3o_signc;

  // check overflow and inexact
  wire s4t_inf = (s4t_exp10c > 10'd254) | s3o_opb_0;
  wire s4t_ovf = s4t_inf & (!s3o_infa) & (!s3o_opb_0);
  wire s4t_ine = (s4t_lost | s4t_ovf)  &
                 (!s3o_opa_0) & (!s3o_opb_0) & (!s3o_infa) & (!s3o_infb);

   // Generate result   
  wire [31:0] s4t_opc;
  assign s4t_opc =
    s4t_opc_nan ? {s4t_nan_sign,QNAN} :
    (s3o_infa | s4t_ovf | s4t_inf) ? {s3o_signc,INF} :
    (s3o_opa_0 | s3o_infb) ?  {s3o_signc,31'd0} :
    (s4t_fract24c_dn | s4t_fract24c_00) ? {s3o_signc,8'd0,s4t_fract24c[22:0]} :
    {s3o_signc,s4t_exp10c[7:0],s4t_fract24c[22:0]};

   // Output Register
  always @(posedge clk) begin
    if(adv_i) begin
      opc_o  <= s4t_opc;
      ine_o  <= s4t_ine;
      inv_o  <= s4t_inv;
      ovf_o  <= (s3o_infa | s4t_ovf | s4t_inf | s4t_opc_nan) & s4t_ine;
      inf_o  <= (s3o_infa | s4t_ovf | s4t_inf) & !s4t_opc_nan;
      unf_o  <= (s3o_opa_0 | s3o_infb | s4t_fract24c_00) & (!s3o_opb_0) & s4t_ine;
      zer_o  <= (s3o_opa_0 | s3o_infb | s4t_fract24c_00) & (!s3o_opb_0);
      dbz_o  <= s3o_opb_0 & (!s3o_opa_0) & (!s4t_inv) & (!s3o_infa);
    end
  end // posedge clock

  // ready is special case
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      ready_o <= 0;
    else if(adv_i)
      ready_o <= s3o_ready;
  end // posedge clock

endmodule // pfpu32_div
