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
   input             signa_i,  // input 'a' related values
   input       [9:0] exp10a_i,
   input      [23:0] fract24a_i,
   input             infa_i,
   input             zeroa_i,
   input             signb_i,  // input 'b' related values
   input       [9:0] exp10b_i,
   input      [23:0] fract24b_i,
   input             infb_i,
   input             zerob_i,
   input             snan_i,   // 'a'/'b' related
   input             qnan_i,
   input             anan_sign_i,
   output reg        div_rdy_o,       // div is ready
   output reg        div_sign_o,      // div signum
   output reg  [9:0] div_exp10_o,     // div exponent
   output reg [23:0] div_fract24_o,   // div fractional
   output reg  [1:0] div_rs_o,        // div round & sticky bits
   output reg        div_inv_o,       // div invalid operation flag
   output reg        div_inf_o,       // div infinity output reg
   output reg        div_snan_o,      // div signaling NaN output reg
   output reg        div_qnan_o,      // div quiet NaN output reg
   output reg        div_anan_sign_o, // div signum for output nan
   output reg        div_dbz_o,       // div division by zero flag
   output reg        div_dbinf_o      // div division by infinity
);

  /*
     Any stage's output is registered.
     Definitions:
       s??o_name - "S"tage number "??", "O"utput
       s??t_name - "S"tage number "??", "T"emporary (internally)
  */


  /* Stage #1: pre-division normalization */

    // detection of some exceptions
    //   0/0, inf/inf -> invalid operation; snan output
  wire s1t_inv = (zeroa_i & zerob_i) | (infa_i & infb_i);
    // division by zero and infinity
  wire s1t_dbz   = (!zeroa_i) & (!infa_i) & zerob_i;
  wire s1t_dbinf = (!zeroa_i) & (!infa_i) & infb_i;
    //   inf input
  wire s1t_inf_i = infa_i;

  // force intermediate results to zero
  wire s1t_fz = zeroa_i | zerob_i | infa_i| infb_i;
  wire [23:0] s1t_fract24a_fz = fract24a_i & {24{!s1t_fz}};
  
  // count leading zeros
  reg [5:0] s1t_dvd_zeros;
  always @(s1t_fract24a_fz)
    casez(s1t_fract24a_fz) // synopsys full_case parallel_case
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
  always @(fract24b_i)
    casez(fract24b_i) // synopsys full_case parallel_case
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
  assign s1t_fracta_lshift_intermediate = s1t_fract24a_fz << s1t_dvd_zeros;
  assign s1t_fractb_lshift_intermediate = fract24b_i << s1t_div_zeros;

  // stage #1 outputs
  //   input related
  reg s1o_inv, s1o_inf_i, s1o_dbz, s1o_dbinf, s1o_fz,
      s1o_snan_i, s1o_qnan_i, s1o_anan_i_sign;
  //   computation related
  reg s1o_sign;
  reg [9:0]  s1o_exp10;
 `ifdef NEW_F32_DIV
  reg [23:0] s1o_fract24a;
  reg [23:0] s1o_fract24b;
 `else
  reg [49:0] s1o_dvdnd_50;
  reg [26:0] s1o_dvsor_27;
 `endif

  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s1o_inv         <= s1t_inv;
      s1o_inf_i       <= s1t_inf_i;
      s1o_dbz         <= s1t_dbz;
      s1o_dbinf       <= s1t_dbinf;
      s1o_fz          <= s1t_fz;
      s1o_snan_i      <= snan_i;
      s1o_qnan_i      <= qnan_i;
      s1o_anan_i_sign <= anan_sign_i;
        // computation related
      s1o_sign     <= signa_i ^ signb_i;
      s1o_exp10    <= (exp10a_i - exp10b_i + 10'd127 -
                       {4'd0,s1t_dvd_zeros} + {4'd0,s1t_div_zeros})
                      & {10{!s1t_fz}};
     `ifdef NEW_F32_DIV
      s1o_fract24a <= s1t_fracta_lshift_intermediate;
      s1o_fract24b <= s1t_fractb_lshift_intermediate;
     `else
      s1o_dvdnd_50 <= {s1t_fracta_lshift_intermediate,26'd0};
      s1o_dvsor_27 <= {3'd0,s1t_fractb_lshift_intermediate};
     `endif
    end // advance
  end // posedge clock

  // ready is special case
  reg s1o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      s1o_ready <= 0;
    else if(flush_i)
      s1o_ready <= 0;
    else if(adv_i)
      s1o_ready <= start_i;
  end // posedge clock

 `ifdef NEW_F32_DIV

  /* Stage #2: division iterations */
  
  // iteration control
  reg [13:0] itr_state; // iteration state indicator
  // special case for (fracta == fractb)
  //wire itr_AeqB = (s1o_fract24a == s1o_fract24b);
  // iteration characteristic points:
  //   condition for enabling iterations
  wire itr_en = |itr_state;
  //   condition for end of iterations
  wire itr_last = itr_state[13];
  // iteration control state machine
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      itr_state <= 14'd0;
    else if(flush_i)
      itr_state <= 14'd0;
    else if(s1o_ready & (!itr_en))
      itr_state <= //itr_AeqB ? {3'd0,1'b1,10'd0} : // force state 10
                              14'd1;              // state 0
    else 
      itr_state <= {itr_state[12:0],1'b0};
  end // posedge clock

  // initial estimation of reciprocal
  //reg  [6:0] s2t_recip7b; // 7-bit in x 7-bit out LUT
  reg  [9:0] s2t_recip10b; // 7-bit in x 10-bit out LUT
  always @(s1o_fract24b[22:16])
    case(s1o_fract24b[22:16]) // synopsys full_case parallel_case
      7'd0 : s2t_recip10b = 10'd1016;
      7'd1 : s2t_recip10b = 10'd1000;
      7'd2 : s2t_recip10b = 10'd985;
      7'd3 : s2t_recip10b = 10'd969;
      7'd4 : s2t_recip10b = 10'd954;
      7'd5 : s2t_recip10b = 10'd940;
      7'd6 : s2t_recip10b = 10'd925;
      7'd7 : s2t_recip10b = 10'd911;
      7'd8 : s2t_recip10b = 10'd896;
      7'd9 : s2t_recip10b = 10'd883;
      7'd10 : s2t_recip10b = 10'd869;
      7'd11 : s2t_recip10b = 10'd855;
      7'd12 : s2t_recip10b = 10'd842;
      7'd13 : s2t_recip10b = 10'd829;
      7'd14 : s2t_recip10b = 10'd816;
      7'd15 : s2t_recip10b = 10'd803;
      7'd16 : s2t_recip10b = 10'd790;
      7'd17 : s2t_recip10b = 10'd778;
      7'd18 : s2t_recip10b = 10'd765;
      7'd19 : s2t_recip10b = 10'd753;
      7'd20 : s2t_recip10b = 10'd741;
      7'd21 : s2t_recip10b = 10'd729;
      7'd22 : s2t_recip10b = 10'd718;
      7'd23 : s2t_recip10b = 10'd706;
      7'd24 : s2t_recip10b = 10'd695;
      7'd25 : s2t_recip10b = 10'd684;
      7'd26 : s2t_recip10b = 10'd673;
      7'd27 : s2t_recip10b = 10'd662;
      7'd28 : s2t_recip10b = 10'd651;
      7'd29 : s2t_recip10b = 10'd640;
      7'd30 : s2t_recip10b = 10'd630;
      7'd31 : s2t_recip10b = 10'd620;
      7'd32 : s2t_recip10b = 10'd609;
      7'd33 : s2t_recip10b = 10'd599;
      7'd34 : s2t_recip10b = 10'd589;
      7'd35 : s2t_recip10b = 10'd579;
      7'd36 : s2t_recip10b = 10'd570;
      7'd37 : s2t_recip10b = 10'd560;
      7'd38 : s2t_recip10b = 10'd550;
      7'd39 : s2t_recip10b = 10'd541;
      7'd40 : s2t_recip10b = 10'd532;
      7'd41 : s2t_recip10b = 10'd523;
      7'd42 : s2t_recip10b = 10'd514;
      7'd43 : s2t_recip10b = 10'd505;
      7'd44 : s2t_recip10b = 10'd496;
      7'd45 : s2t_recip10b = 10'd487;
      7'd46 : s2t_recip10b = 10'd478;
      7'd47 : s2t_recip10b = 10'd470;
      7'd48 : s2t_recip10b = 10'd461;
      7'd49 : s2t_recip10b = 10'd453;
      7'd50 : s2t_recip10b = 10'd445;
      7'd51 : s2t_recip10b = 10'd436;
      7'd52 : s2t_recip10b = 10'd428;
      7'd53 : s2t_recip10b = 10'd420;
      7'd54 : s2t_recip10b = 10'd412;
      7'd55 : s2t_recip10b = 10'd405;
      7'd56 : s2t_recip10b = 10'd397;
      7'd57 : s2t_recip10b = 10'd389;
      7'd58 : s2t_recip10b = 10'd382;
      7'd59 : s2t_recip10b = 10'd374;
      7'd60 : s2t_recip10b = 10'd367;
      7'd61 : s2t_recip10b = 10'd359;
      7'd62 : s2t_recip10b = 10'd352;
      7'd63 : s2t_recip10b = 10'd345;
      7'd64 : s2t_recip10b = 10'd338;
      7'd65 : s2t_recip10b = 10'd331;
      7'd66 : s2t_recip10b = 10'd324;
      7'd67 : s2t_recip10b = 10'd317;
      7'd68 : s2t_recip10b = 10'd310;
      7'd69 : s2t_recip10b = 10'd303;
      7'd70 : s2t_recip10b = 10'd297;
      7'd71 : s2t_recip10b = 10'd290;
      7'd72 : s2t_recip10b = 10'd283;
      7'd73 : s2t_recip10b = 10'd277;
      7'd74 : s2t_recip10b = 10'd271;
      7'd75 : s2t_recip10b = 10'd264;
      7'd76 : s2t_recip10b = 10'd258;
      7'd77 : s2t_recip10b = 10'd252;
      7'd78 : s2t_recip10b = 10'd245;
      7'd79 : s2t_recip10b = 10'd239;
      7'd80 : s2t_recip10b = 10'd233;
      7'd81 : s2t_recip10b = 10'd227;
      7'd82 : s2t_recip10b = 10'd221;
      7'd83 : s2t_recip10b = 10'd215;
      7'd84 : s2t_recip10b = 10'd210;
      7'd85 : s2t_recip10b = 10'd204;
      7'd86 : s2t_recip10b = 10'd198;
      7'd87 : s2t_recip10b = 10'd192;
      7'd88 : s2t_recip10b = 10'd187;
      7'd89 : s2t_recip10b = 10'd181;
      7'd90 : s2t_recip10b = 10'd176;
      7'd91 : s2t_recip10b = 10'd170;
      7'd92 : s2t_recip10b = 10'd165;
      7'd93 : s2t_recip10b = 10'd159;
      7'd94 : s2t_recip10b = 10'd154;
      7'd95 : s2t_recip10b = 10'd149;
      7'd96 : s2t_recip10b = 10'd144;
      7'd97 : s2t_recip10b = 10'd139;
      7'd98 : s2t_recip10b = 10'd133;
      7'd99 : s2t_recip10b = 10'd128;
      7'd100 : s2t_recip10b = 10'd123;
      7'd101 : s2t_recip10b = 10'd118;
      7'd102 : s2t_recip10b = 10'd113;
      7'd103 : s2t_recip10b = 10'd108;
      7'd104 : s2t_recip10b = 10'd104;
      7'd105 : s2t_recip10b = 10'd99;
      7'd106 : s2t_recip10b = 10'd94;
      7'd107 : s2t_recip10b = 10'd89;
      7'd108 : s2t_recip10b = 10'd84;
      7'd109 : s2t_recip10b = 10'd80;
      7'd110 : s2t_recip10b = 10'd75;
      7'd111 : s2t_recip10b = 10'd71;
      7'd112 : s2t_recip10b = 10'd66;
      7'd113 : s2t_recip10b = 10'd61;
      7'd114 : s2t_recip10b = 10'd57;
      7'd115 : s2t_recip10b = 10'd53;
      7'd116 : s2t_recip10b = 10'd48;
      7'd117 : s2t_recip10b = 10'd44;
      7'd118 : s2t_recip10b = 10'd39;
      7'd119 : s2t_recip10b = 10'd35;
      7'd120 : s2t_recip10b = 10'd31;
      7'd121 : s2t_recip10b = 10'd27;
      7'd122 : s2t_recip10b = 10'd22;
      7'd123 : s2t_recip10b = 10'd18;
      7'd124 : s2t_recip10b = 10'd14;
      7'd125 : s2t_recip10b = 10'd10;
      7'd126 : s2t_recip10b = 10'd6;
      7'd127 : s2t_recip10b = 10'd2;
    endcase // 7-bit LUT for initial approximation of reciprocal

  // reciprocal with restored leading 01
  //wire [8:0] s2t_recip9b =
   // special case: the exacly '1' is converted to the exacly '1'
   //(s1o_fract24b[23] & (!(|s1o_fract24b[22:0]))) ? 9'b100000000 :
   // restore leading '01'
   //                                                {2'b01,s2t_recip7b};
  wire [11:0] s2t_recip12b =
   // special case: the exacly '1' is converted to the exacly '1'
   (s1o_fract24b[23] & (!(|s1o_fract24b[22:0]))) ? 12'h800 :
   // restore leading '01'
                                                   {2'b01,s2t_recip10b};


  // the subsequent two stages multiplier operates with 32-bit inputs
  // 25-bits: fractionals (quotient is in range 0.5 to 1)
  //  1-bit : rounding bit
  //  6-bits: guard (due to truncations of intermediate results)


  // intermediate results:
  //   updated divisor (D) is rounded up while all other intermediate values
  //   are just truncated in according with directed roundings analysed in:
  //     Guy Even, Peter-M.Seidel, Warren E.Ferguson
  //     "A parametric error analysis of Goldschmidt’s division algorithm"
  wire itr_rndD = itr_state[3] | itr_state[6];
  //   round quotient up to provide convergence to reminder free result
  wire itr_rndN = itr_state[10];
  //   N (dividend) or D (divisor)
  wire [33:0] itr_NorD34;
  //   'F' (2-D) or 'Reminder'
  wire [32:0] itr_ForR33;


  // control for multiplier's input 'a'
  wire itr_uinA = itr_state[0] | itr_state[1] |
                  itr_state[3] | itr_state[4] |
                  itr_state[6] | itr_state[7] |
                  itr_state[10];
  // multiplexer for multiplier's input 'a'
  wire [31:0] s2t_mul32a =
    (itr_state[0] | itr_state[10]) ? {s1o_fract24b,8'd0} :
     itr_state[1]                  ? {s1o_fract24a,8'd0} :
                                     itr_NorD34[32:1];
  // register of multiplier's input 'a'
  reg [31:0] s2r_fract32a;
  always @(posedge clk) begin
    if(itr_uinA)
      s2r_fract32a <= s2t_mul32a;
  end // posedge clock


  // control for multiplier's input 'b'
  //   the register also contains quotient to output
  wire itr_uinB = itr_state[0] | itr_state[3] | itr_state[6] | itr_state[10];
  // multiplexer for multiplier's input 'b'
  wire [31:0] s2t_mul32b =
     //itr_AeqB      ? 32'h80000000            : // force quotient to "1"
     //itr_state[0]  ? {s2t_recip9b,23'd0}     :
     itr_state[0]  ? {s2t_recip12b,20'd0}     :
     itr_state[10] ? {itr_NorD34[32:8],7'd0} : // compute reminder
                     itr_ForR33[31:0];
  // register of multiplier's input 'b'
  reg [31:0] s2r_fract32b;
  // registering
  always @(posedge clk) begin
    if(itr_uinB)
      s2r_fract32b <= s2t_mul32b;
  end // posedge clock


  /* 1st stage of multiplier */

  // computation related fractionals
  //  insert leading zeros to signal unsigned values
  //  for potential usage DSP blocks of a FPGA
  wire [16:0] m1t_fract17_al = {1'b0, s2r_fract32a[15: 0]};
  wire [16:0] m1t_fract17_ah = {1'b0, s2r_fract32a[31:16]};
  wire [16:0] m1t_fract17_bl = {1'b0, s2r_fract32b[15: 0]};
  wire [16:0] m1t_fract17_bh = {1'b0, s2r_fract32b[31:16]};

  // partial products
  reg [33:0] m1o_fract34_albl;
  reg [33:0] m1o_fract34_albh;
  reg [33:0] m1o_fract34_ahbl;
  reg [33:0] m1o_fract34_ahbh;
  //   registering
  always @(posedge clk) begin
    if(adv_i | itr_en) begin
      m1o_fract34_albl <= m1t_fract17_al * m1t_fract17_bl;
      m1o_fract34_albh <= m1t_fract17_al * m1t_fract17_bh;
      m1o_fract34_ahbl <= m1t_fract17_ah * m1t_fract17_bl;
      m1o_fract34_ahbh <= m1t_fract17_ah * m1t_fract17_bh;
    end // advance pipe
  end // posedge clock


  /* 2nd stage of multiplier */
  wire [63:0] m2t_fract64;
  assign m2t_fract64 = {m1o_fract34_ahbh[31:0],  32'd0} +
                       {14'd0, m1o_fract34_ahbl, 16'd0} +
                       {14'd0, m1o_fract34_albh, 16'd0} +
                       {32'd0,  m1o_fract34_albl[31:0]};

  // full product
  reg [63:0] m2o_fract64;
  //   registering
  always @(posedge clk) begin
    if(adv_i | itr_en) begin
      m2o_fract64 <= m2t_fract64;
    end // advance pipe
  end // posedge clock


  /* Intermediate results of Goldshmidt's iterations */

  // compute 2's complement or reminder (for sticky bit detection)
  // pay attantion that point position is located just after bit [30]
  wire [31:0] itr_AorT32 =
    itr_last ? {1'b0,s1o_fract24a,7'd0} :  // for reminder
               (32'h80000000);             // for two's complement
                                    
  // intermediate N (dividend) or D (divisor)
  // binary point position is located just after bit [31]
  //assign itr_NorD33 = m2o_fract64[63:31] + 
  //                    {27'd0,itr_rndN,4'd0,          // round up for reminder free case support
  //                    (itr_rndD & m2o_fract64[31])}; // round up stops effictive computations if precision is achived
  assign itr_NorD34 = m2o_fract64[63:30] + 
                      {33'd0,(itr_rndN | itr_rndD) & m2o_fract64[30]}; 

  // 'F' or 'Reminder' (on the last stage NorD = B * Q)
  assign itr_ForR33 = {itr_AorT32,1'b0} - itr_NorD34[33:1];
 `else

  /* Stage #2: division */

  localparam STATE_WAITING = 1'b0,
             STATE_BUSY    = 1'b1;

  reg       s2t_ready;
  reg       s2t_state;
  reg [4:0] s2t_count;

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      s2t_state <= STATE_WAITING;
      s2t_ready <= 1'b0;
    end
    else if(flush_i) begin
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
    if(rst) begin
      s2t_qutnt <= 1'b0;
      s2t_rmndr <= 1'b0;
    end
    else if (flush_i) begin
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
 `endif

  // stage #2 outputs
  //   input related
  reg s2o_inv, s2o_inf_i, s2o_dbz, s2o_dbinf, s2o_fz,
      s2o_snan_i, s2o_qnan_i, s2o_anan_i_sign;
  //   computation related
  reg        s2o_sign;
  reg [9:0]  s2o_exp10;
  reg [26:0] s2o_qutnt;

  //   registering
  always @(posedge clk) begin
   `ifdef NEW_F32_DIV
    if(itr_last)
   `else
    if(adv_i)
   `endif
    begin
        // input related
      s2o_inv         <= s1o_inv;
      s2o_inf_i       <= s1o_inf_i;
      s2o_dbz         <= s1o_dbz;
      s2o_dbinf       <= s1o_dbinf;
      s2o_fz          <= s1o_fz;
      s2o_snan_i      <= s1o_snan_i;
      s2o_qnan_i      <= s1o_qnan_i;
      s2o_anan_i_sign <= s1o_anan_i_sign;
        // computation related
      s2o_sign  <= s1o_sign;
      s2o_exp10 <= s1o_exp10;
     `ifdef NEW_F32_DIV
      s2o_qutnt <= {s2r_fract32b[31:7],(|itr_ForR33)}
                   & {26{!s1o_fz}};
     `else
      s2o_qutnt <= {s2t_qutnt[26:1],(s2t_qutnt[0] | (|s2t_rmndr))}
                   & {27{!s1o_fz}};
     `endif
    end // (reset or flush) / advance
  end // posedge clock

  // ready is special case
  reg s2o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      s2o_ready <= 0;
    else if(flush_i)
      s2o_ready <= 0;
   `ifdef NEW_F32_DIV
    else if(adv_i | itr_last)
      s2o_ready <= itr_last;
   `else
    else if(adv_i)
      s2o_ready <= s2t_ready;
   `endif
  end // posedge clock


  /* Stage #3: calc align values */  

  // qutnt
  // 26 25                    2
  // |  |                     |
  // h  ffffffffffffffffffffffg rs
  // 1. xxxx...
  // 0. 1xxx...

  // rigt shift value
  // and appropriatelly corrected exponent
  wire s2o_exp10_0 = !(|s2o_exp10);
  wire [9:0] s3t_shr_of_neg_exp = 11'h401 - {1'b0,s2o_exp10}; // 1024-v+1
  //...
  wire [9:0] s3t_shrx;
  wire [9:0] s3t_exp10rx;
  assign {s3t_shrx,s3t_exp10rx} =
      // zero result case
    s2o_fz                  ? {10'd0,10'd0} :
      // zero exponent sum (denorm. result potentially)
    (!s2o_fz & s2o_exp10_0) ? {10'd1,10'd1} :
      // negative exponent sum
      //  (!) takes carry into account automatically
    s2o_exp10[9]            ? {s3t_shr_of_neg_exp,10'd1} :
      // normal case at last
                              {10'd0,s2o_exp10};
  // max. right shift that makes sense is 26bits
  //  i.e. [26] moves to sticky position: ([0])
  wire [5:0] s3t_shr = (s3t_shrx > 10'd26) ? 6'd26 : s3t_shrx[5:0];

  // in fact, as the dividend and divisor was normalized
  // and the result is non-zero
  // the '1' is maximum number of leading zeros in the quotient
  wire s3t_nlz = !s2o_qutnt[26];
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
  wire [26:0] s3t_fract27 =
    (|s3t_shr) ? (s2o_qutnt >> s3t_shr) :
                 (s2o_qutnt << s3t_shlx);

  // sticky bit computation for right shift
  // max. right shift that makes sense i 26bits
  //  i.e. [26] moves to sticky position: ([0])
  reg s3t_sticky_shr;
  always @(s3t_shr or s2o_qutnt) begin
    case(s3t_shr)
      6'd0   : s3t_sticky_shr = |s2o_qutnt[ 1:0];
      6'd1   : s3t_sticky_shr = |s2o_qutnt[ 2:0];
      6'd2   : s3t_sticky_shr = |s2o_qutnt[ 3:0];
      6'd3   : s3t_sticky_shr = |s2o_qutnt[ 4:0];
      6'd4   : s3t_sticky_shr = |s2o_qutnt[ 5:0];
      6'd5   : s3t_sticky_shr = |s2o_qutnt[ 6:0];
      6'd6   : s3t_sticky_shr = |s2o_qutnt[ 7:0];
      6'd7   : s3t_sticky_shr = |s2o_qutnt[ 8:0];
      6'd8   : s3t_sticky_shr = |s2o_qutnt[ 9:0];
      6'd9   : s3t_sticky_shr = |s2o_qutnt[10:0];
      6'd10  : s3t_sticky_shr = |s2o_qutnt[11:0];
      6'd11  : s3t_sticky_shr = |s2o_qutnt[12:0];
      6'd12  : s3t_sticky_shr = |s2o_qutnt[13:0];
      6'd13  : s3t_sticky_shr = |s2o_qutnt[14:0];
      6'd14  : s3t_sticky_shr = |s2o_qutnt[15:0];
      6'd15  : s3t_sticky_shr = |s2o_qutnt[16:0];
      6'd16  : s3t_sticky_shr = |s2o_qutnt[17:0];
      6'd17  : s3t_sticky_shr = |s2o_qutnt[18:0];
      6'd18  : s3t_sticky_shr = |s2o_qutnt[19:0];
      6'd19  : s3t_sticky_shr = |s2o_qutnt[20:0];
      6'd20  : s3t_sticky_shr = |s2o_qutnt[21:0];
      6'd21  : s3t_sticky_shr = |s2o_qutnt[22:0];
      6'd22  : s3t_sticky_shr = |s2o_qutnt[23:0];
      6'd23  : s3t_sticky_shr = |s2o_qutnt[24:0];
      6'd24  : s3t_sticky_shr = |s2o_qutnt[25:0];
      default: s3t_sticky_shr = |s2o_qutnt[26:0];
    endcase
  end // always

  wire s3t_sticky = (|s3t_shr) ? s3t_sticky_shr : (|s3t_fract27[1:0]);


  // registering output
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      div_inv_o       <= s2o_inv;
      div_inf_o       <= s2o_inf_i;
      div_dbz_o       <= s2o_dbz;
      div_dbinf_o     <= s2o_dbinf;
      div_snan_o      <= s2o_snan_i;
      div_qnan_o      <= s2o_qnan_i;
      div_anan_sign_o <= s2o_anan_i_sign;
        // computation related
      div_sign_o    <= s2o_sign;
      div_exp10_o   <= (|s3t_shr) ? s3t_exp10rx : s3t_exp10lx;
      div_fract24_o <= s3t_fract27[26:3];
      div_rs_o      <= {s3t_fract27[2],s3t_sticky};
    end // advance
  end // posedge clock

  // ready is special case
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      div_rdy_o <= 0;
    else if(flush_i)
      div_rdy_o <= 0;
    else if(adv_i)
      div_rdy_o <= s2o_ready;
  end // posedge clock

endmodule // pfpu32_div
