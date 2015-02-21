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
   output reg        div_sign_rmnd_o, // signum or reminder for IEEE compliant rounding
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

  // Goldshmidt iterations control
  reg [13:0] itr_state; // iteration state indicator
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
    else if(start_i & (!itr_en))
      itr_state <= 14'd1;
    else 
      itr_state <= {itr_state[12:0],1'b0};
  end // posedge clock

  // stage #1 outputs
  //   input related
  reg s1o_inv, s1o_inf_i, s1o_dbz, s1o_dbinf, s1o_fz,
      s1o_snan_i, s1o_qnan_i, s1o_anan_i_sign;
  //   computation related
  reg s1o_sign;
  reg [9:0]  s1o_exp10;
  reg [23:0] s1o_fract24a;
  reg [23:0] s1o_fract24b;
  //   registering
  always @(posedge clk) begin
    if(adv_i & (!itr_en)) begin
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
      s1o_fract24a <= s1t_fracta_lshift_intermediate;
      s1o_fract24b <= s1t_fractb_lshift_intermediate;
    end // advance
  end // posedge clock


  /* Stage #2: division iterations */
  
  
  // initial estimation of reciprocal
  wire [8:0] s2t_recip9b;
  reciprocal_lut u_rlut
  (
    .b_i(s1o_fract24b[22:16]),
    .r_o(s2t_recip9b)
  );
  // support case: b==1
  wire b_eq_1 = s1o_fract24b[23] & (!(|s1o_fract24b[22:0]));
  // reciprocal with restored leading 01
  wire [10:0] s2t_recip11b = b_eq_1 ?  11'b10000000000 :
                                      {2'b01,s2t_recip9b};

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
  wire itr_rndDvsr;
  //   align resulting quotient to support subsequent IEEE-compliant rounding
  wire itr_rndQ = itr_state[10];
  wire itr_rndQ1xx, itr_rndQ01x;
  //   N (dividend) or D (divisor)
  wire [32:0] itr_qtnt33;
  //   'F' (2-D) or 'Reminder'
  wire [32:0] itr_rmnd33;


  // control for multiplier's input 'A'
  //   the register also contains quotient to output
  wire itr_uinA = itr_state[0] | itr_state[3] | itr_state[6] | itr_state[10];
  // multiplexer for multiplier's input 'A'
  wire [31:0] s2t_mul32a =
     itr_state[0]                 ? {s2t_recip11b,21'd0}    :
    (itr_state[10] & itr_rndQ1xx) ? {itr_qtnt33[31:7],7'd0} : // truncate by 2^(-n-1)
    (itr_state[10] & itr_rndQ01x) ? {itr_qtnt33[31:6],6'd0} : // truncate by 2^(-n-1)
                                     itr_rmnd33[31:0];
  // register of multiplier's input 'A'
  reg [31:0] s2r_fract32a;
  // registering
  always @(posedge clk) begin
    if(itr_uinA)
      s2r_fract32a <= s2t_mul32a;
  end // posedge clock


  // control for multiplier's input 'B'
  wire itr_uinB = itr_state[0] | itr_state[1] |
                  itr_state[3] | itr_state[4] |
                  itr_state[6] | itr_state[7] |
                  itr_state[10];
  // multiplexer for multiplier's input 'B'
  wire [31:0] s2t_mul32b =
    (itr_state[0] | itr_state[10]) ? {s1o_fract24b,8'd0} :
     itr_state[1]                  ? {s1o_fract24a,8'd0} :
                                      itr_qtnt33[31:0];
  // register of multiplier's input 'B'
  reg [31:0] s2r_fract32b;
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

  // take into account the truncated part multiplier's output
  wire itr_rs_fract64 = |m2o_fract64[30:0];
                                    
  // Feedback from multiplier's output with various rounding tecqs.
  //   +2^(-n-2) in case of rounding 1.xxx qutient
  assign itr_rndQ1xx = itr_rndQ &   m2o_fract64[62];
  //   +2^(-n-2) in case of rounding 0.1xx qutient
  assign itr_rndQ01x = itr_rndQ & (!m2o_fract64[62]);
  //   directed rounding of intermediate divisor 'D'
  assign itr_rndDvsr = itr_rndD &   itr_rs_fract64;
  //   rounding mask:
  wire [32:0] itr_rndM33 = 
    {26'd0,itr_rndQ1xx,itr_rndQ01x,4'd0,itr_rndDvsr}; // bits [6],[5] ... [0]
  //   rounding
  assign itr_qtnt33 = m2o_fract64[63:31] + itr_rndM33; 


  // compute 2's complement or reminder (for sticky bit detection)
  // binary point position is located just after bit [30]
  wire [32:0] itr_AorT33 =
    itr_last ? {1'b0,s1o_fract24a,8'd0} : // for reminder
               {32'h80000000,1'b0};       // for two's complement

  // 'Reminder' / Two's complement
  assign itr_rmnd33 = itr_AorT33 - itr_qtnt33;
  wire   itr_sticky = |itr_rmnd33;
  
  // Additionally store 26-bit of non-rounded reminder.
  // It is used for rounding in cases of denormalized result.
  // Stiky bit is forced to be zero
  reg [26:0] s2o_raw_qtnt;
  always @(posedge clk) begin
    if(itr_rndQ)
      s2o_raw_qtnt <= {m2o_fract64[62:37],1'b0};
  end

  // stage #2 outputs
  //   input related
  reg s2o_inv, s2o_inf_i, s2o_dbz, s2o_dbinf, s2o_fz,
      s2o_snan_i, s2o_qnan_i, s2o_anan_i_sign;
  //   computation related
  reg        s2o_sign;
  reg [9:0]  s2o_exp10;
  reg [26:0] s2o_qutnt;
  reg        s2o_sign_rmnd;

  //   registering
  always @(posedge clk) begin
    if(itr_last)
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
      s2o_qutnt <= {s2r_fract32a[31:6],(itr_sticky | itr_rs_fract64)}
                   & {27{!s1o_fz}};
      s2o_sign_rmnd <= itr_rmnd33[32] | ((~itr_sticky) & itr_rs_fract64);
    end // (reset or flush) / advance
  end // posedge clock

  // ready is special case
  reg s2o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      s2o_ready <= 0;
    else if(flush_i)
      s2o_ready <= 0;
    else if(adv_i | itr_last)
      s2o_ready <= itr_last;
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
  // variants:
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
  wire s3t_is_shr = |s3t_shr;

  // in fact, as the dividend and divisor was normalized
  // and the result is non-zero
  // the '1' is maximum number of leading zeros in the quotient
  wire s3t_nlz = ~s2o_qutnt[26];
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

  // flags that rounded quotient is exact quotient
  wire s3t_qtnt_exact = ~s2o_qutnt[0];
  // check if result is denormalized
  wire s3t_is_shl = |s3t_shlx;
  wire s3t_denorm = s3t_is_shr | 
                    ((~s3t_is_shr) & (~s3t_is_shl) & s3t_nlz);
  // Select quotient for subsequent align and rounding  
  // Denormalized and non-exact results are based on raw-quotient
  wire [26:0] s3t_shqtnt =
    ( (~s3t_denorm) | s3t_qtnt_exact | 
      ((~s3t_qtnt_exact) & (~s2o_sign_rmnd)) ) ?
      s2o_qutnt : {s2o_raw_qtnt[26:1],1'b1};

  // align
  wire [26:0] s3t_fract27 =
    (s3t_is_shr) ? (s3t_shqtnt >> s3t_shr) :
                   (s3t_shqtnt << s3t_shlx);
                   
  // sticky bit computation for right shift
  // max. right shift that makes sense is 26bits
  //  i.e. [26] moves to sticky position: ([0])
  reg s3t_sticky_shr;
  always @(s3t_shr or s3t_shqtnt) begin
    case(s3t_shr)
      6'd0   : s3t_sticky_shr = |s3t_shqtnt[ 1:0];
      6'd1   : s3t_sticky_shr = |s3t_shqtnt[ 2:0];
      6'd2   : s3t_sticky_shr = |s3t_shqtnt[ 3:0];
      6'd3   : s3t_sticky_shr = |s3t_shqtnt[ 4:0];
      6'd4   : s3t_sticky_shr = |s3t_shqtnt[ 5:0];
      6'd5   : s3t_sticky_shr = |s3t_shqtnt[ 6:0];
      6'd6   : s3t_sticky_shr = |s3t_shqtnt[ 7:0];
      6'd7   : s3t_sticky_shr = |s3t_shqtnt[ 8:0];
      6'd8   : s3t_sticky_shr = |s3t_shqtnt[ 9:0];
      6'd9   : s3t_sticky_shr = |s3t_shqtnt[10:0];
      6'd10  : s3t_sticky_shr = |s3t_shqtnt[11:0];
      6'd11  : s3t_sticky_shr = |s3t_shqtnt[12:0];
      6'd12  : s3t_sticky_shr = |s3t_shqtnt[13:0];
      6'd13  : s3t_sticky_shr = |s3t_shqtnt[14:0];
      6'd14  : s3t_sticky_shr = |s3t_shqtnt[15:0];
      6'd15  : s3t_sticky_shr = |s3t_shqtnt[16:0];
      6'd16  : s3t_sticky_shr = |s3t_shqtnt[17:0];
      6'd17  : s3t_sticky_shr = |s3t_shqtnt[18:0];
      6'd18  : s3t_sticky_shr = |s3t_shqtnt[19:0];
      6'd19  : s3t_sticky_shr = |s3t_shqtnt[20:0];
      6'd20  : s3t_sticky_shr = |s3t_shqtnt[21:0];
      6'd21  : s3t_sticky_shr = |s3t_shqtnt[22:0];
      6'd22  : s3t_sticky_shr = |s3t_shqtnt[23:0];
      6'd23  : s3t_sticky_shr = |s3t_shqtnt[24:0];
      6'd24  : s3t_sticky_shr = |s3t_shqtnt[25:0];
      default: s3t_sticky_shr = |s3t_shqtnt[26:0];
    endcase
  end // always

  wire s3t_sticky = (s3t_is_shr) ? s3t_sticky_shr : (|s3t_fract27[1:0]);

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
      div_exp10_o   <= (s3t_is_shr) ? s3t_exp10rx : s3t_exp10lx;
      div_fract24_o <= s3t_fract27[26:3];
      div_rs_o      <= {s3t_fract27[2],s3t_sticky};
      div_sign_rmnd_o <= s2o_sign_rmnd;
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


// initial reciprocal approximation
module reciprocal_lut 
(
  input      [6:0] b_i,
  output reg [8:0] r_o
);
  always @(b_i) begin
    case(b_i) // synopsys full_case parallel_case
      7'd0   : r_o = 9'd508;
      7'd1   : r_o = 9'd500;
      7'd2   : r_o = 9'd492;
      7'd3   : r_o = 9'd485;
      7'd4   : r_o = 9'd477;
      7'd5   : r_o = 9'd470;
      7'd6   : r_o = 9'd463;
      7'd7   : r_o = 9'd455;
      7'd8   : r_o = 9'd448;
      7'd9   : r_o = 9'd441;
      7'd10  : r_o = 9'd434;
      7'd11  : r_o = 9'd428;
      7'd12  : r_o = 9'd421;
      7'd13  : r_o = 9'd414;
      7'd14  : r_o = 9'd408;
      7'd15  : r_o = 9'd401;
      7'd16  : r_o = 9'd395;
      7'd17  : r_o = 9'd389;
      7'd18  : r_o = 9'd383;
      7'd19  : r_o = 9'd377;
      7'd20  : r_o = 9'd371;
      7'd21  : r_o = 9'd365;
      7'd22  : r_o = 9'd359;
      7'd23  : r_o = 9'd353;
      7'd24  : r_o = 9'd347;
      7'd25  : r_o = 9'd342;
      7'd26  : r_o = 9'd336;
      7'd27  : r_o = 9'd331;
      7'd28  : r_o = 9'd326;
      7'd29  : r_o = 9'd320;
      7'd30  : r_o = 9'd315;
      7'd31  : r_o = 9'd310;
      7'd32  : r_o = 9'd305;
      7'd33  : r_o = 9'd300;
      7'd34  : r_o = 9'd295;
      7'd35  : r_o = 9'd290;
      7'd36  : r_o = 9'd285;
      7'd37  : r_o = 9'd280;
      7'd38  : r_o = 9'd275;
      7'd39  : r_o = 9'd271;
      7'd40  : r_o = 9'd266;
      7'd41  : r_o = 9'd261;
      7'd42  : r_o = 9'd257;
      7'd43  : r_o = 9'd252;
      7'd44  : r_o = 9'd248;
      7'd45  : r_o = 9'd243;
      7'd46  : r_o = 9'd239;
      7'd47  : r_o = 9'd235;
      7'd48  : r_o = 9'd231;
      7'd49  : r_o = 9'd226;
      7'd50  : r_o = 9'd222;
      7'd51  : r_o = 9'd218;
      7'd52  : r_o = 9'd214;
      7'd53  : r_o = 9'd210;
      7'd54  : r_o = 9'd206;
      7'd55  : r_o = 9'd202;
      7'd56  : r_o = 9'd198;
      7'd57  : r_o = 9'd195;
      7'd58  : r_o = 9'd191;
      7'd59  : r_o = 9'd187;
      7'd60  : r_o = 9'd183;
      7'd61  : r_o = 9'd180;
      7'd62  : r_o = 9'd176;
      7'd63  : r_o = 9'd172;
      7'd64  : r_o = 9'd169;
      7'd65  : r_o = 9'd165;
      7'd66  : r_o = 9'd162;
      7'd67  : r_o = 9'd158;
      7'd68  : r_o = 9'd155;
      7'd69  : r_o = 9'd152;
      7'd70  : r_o = 9'd148;
      7'd71  : r_o = 9'd145;
      7'd72  : r_o = 9'd142;
      7'd73  : r_o = 9'd138;
      7'd74  : r_o = 9'd135;
      7'd75  : r_o = 9'd132;
      7'd76  : r_o = 9'd129;
      7'd77  : r_o = 9'd126;
      7'd78  : r_o = 9'd123;
      7'd79  : r_o = 9'd120;
      7'd80  : r_o = 9'd117;
      7'd81  : r_o = 9'd114;
      7'd82  : r_o = 9'd111;
      7'd83  : r_o = 9'd108;
      7'd84  : r_o = 9'd105;
      7'd85  : r_o = 9'd102;
      7'd86  : r_o = 9'd99;
      7'd87  : r_o = 9'd96;
      7'd88  : r_o = 9'd93;
      7'd89  : r_o = 9'd91;
      7'd90  : r_o = 9'd88;
      7'd91  : r_o = 9'd85;
      7'd92  : r_o = 9'd82;
      7'd93  : r_o = 9'd80;
      7'd94  : r_o = 9'd77;
      7'd95  : r_o = 9'd74;
      7'd96  : r_o = 9'd72;
      7'd97  : r_o = 9'd69;
      7'd98  : r_o = 9'd67;
      7'd99  : r_o = 9'd64;
      7'd100 : r_o = 9'd62;
      7'd101 : r_o = 9'd59;
      7'd102 : r_o = 9'd57;
      7'd103 : r_o = 9'd54;
      7'd104 : r_o = 9'd52;
      7'd105 : r_o = 9'd49;
      7'd106 : r_o = 9'd47;
      7'd107 : r_o = 9'd45;
      7'd108 : r_o = 9'd42;
      7'd109 : r_o = 9'd40;
      7'd110 : r_o = 9'd38;
      7'd111 : r_o = 9'd35;
      7'd112 : r_o = 9'd33;
      7'd113 : r_o = 9'd31;
      7'd114 : r_o = 9'd29;
      7'd115 : r_o = 9'd26;
      7'd116 : r_o = 9'd24;
      7'd117 : r_o = 9'd22;
      7'd118 : r_o = 9'd20;
      7'd119 : r_o = 9'd18;
      7'd120 : r_o = 9'd15;
      7'd121 : r_o = 9'd13;
      7'd122 : r_o = 9'd11;
      7'd123 : r_o = 9'd9;
      7'd124 : r_o = 9'd7;
      7'd125 : r_o = 9'd5;
      7'd126 : r_o = 9'd3;
      default: r_o = 9'd1;
    endcase // LUT for initial approximation of reciprocal
  end // always
endmodule 
