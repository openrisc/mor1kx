//////////////////////////////////////////////////////////////////////
//                                                                  //
//    pfpu32_mul                                                    //
//                                                                  //
//    This file is part of the mor1kx project                       //
//    https://github.com/openrisc/mor1kx                            //
//                                                                  //
//    Description                                                   //
//    multiplier pipeline for single precision floating             //
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

module pfpu32_mul
(
   input             clk,
   input             rst,
   input             flush_i,  // flushe pipe
   input             adv_i,    // advance pipe
   input             start_i,  // start multiplier
   input       [1:0] rmode_i,  // round mode
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
   output reg [31:0] opc_o,
   output reg        ine_o,
   output reg        inv_o,    // 0 * inf -> invalid and qnan
   output reg        ovf_o,
   output reg        inf_o,
   output reg        unf_o,
   output reg        zer_o,    // zero rezult
   output reg        ready_o
);

  localparam INF  = 31'b1111111100000000000000000000000;
  localparam QNAN = 31'b1111111110000000000000000000000;
  localparam SNAN = 31'b1111111101111111111111111111111;

  /*
     Any stage's output is registered.
     Definitions:
       s??o_name - "S"tage number "??", "O"utput
       s??t_name - "S"tage number "??", "T"emporary (internally)
  */


  /* Stage #1: pre-multiplier stage */

    // detection of some exceptions
    //   0 * inf -> invalid operation; snan output
  wire s1t_inv = (zeroa_i & infb_i) | (zerob_i & infa_i);
    //   inf input
  wire s1t_inf_i = infa_i | infb_i;

    // result is zero
  wire s1t_opc_0 = zeroa_i | zerob_i;
  
    // computation related exponent
  wire [9:0] s1t_exp10c = (exp10a_i + exp10b_i - 10'd127)
                           & {10{!s1t_opc_0}};
  
    // computation related fractionals
    //  insert leading zeros to signal unsigned values
    //  for potential usage DSP blocks of a FPGA
  wire [12:0] s1t_fract13_al = {1'b0, fract24a_i[11: 0]};
  wire [12:0] s1t_fract13_ah = {1'b0, fract24a_i[23:12]};
  wire [12:0] s1t_fract13_bl = {1'b0, fract24b_i[11: 0]};
  wire [12:0] s1t_fract13_bh = {1'b0, fract24b_i[23:12]};
  
   
  // stage #1 outputs
  //   input related
  reg s1o_inv, s1o_inf_i,
      s1o_snan_i, s1o_qnan_i, s1o_anan_i_sign;
  //   computation related
  reg        s1o_opc_0;
  reg        s1o_signc;
  reg [9:0]  s1o_exp10c;
  reg [25:0] s1o_fract26_albl;
  reg [25:0] s1o_fract26_albh;
  reg [25:0] s1o_fract26_ahbl;
  reg [25:0] s1o_fract26_ahbh;
 
  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s1o_inv         <= s1t_inv;
      s1o_inf_i       <= s1t_inf_i;
      s1o_snan_i      <= snan_i;
      s1o_qnan_i      <= qnan_i;
      s1o_anan_i_sign <= anan_sign_i;
        // computation related
      s1o_opc_0  <= s1t_opc_0;
      s1o_signc  <= signa_i ^ signb_i;
      s1o_exp10c <= s1t_exp10c;
      s1o_fract26_albl <= s1t_fract13_al * s1t_fract13_bl;
      s1o_fract26_albh <= s1t_fract13_al * s1t_fract13_bh;
      s1o_fract26_ahbl <= s1t_fract13_ah * s1t_fract13_bl;
      s1o_fract26_ahbh <= s1t_fract13_ah * s1t_fract13_bh;
    end // advance pipe
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


  /* Stage #2: multiplier end */

  wire  [47:0] s2t_fract48;
  assign s2t_fract48 = {s1o_fract26_ahbh[23:0],  24'd0} +
                       {10'd0, s1o_fract26_ahbl, 12'd0} +
                       {10'd0, s1o_fract26_albh, 12'd0} +
                       {24'd0,  s1o_fract26_albl[23:0]};

   wire [9:0] s2t_carry10 = {9'd0,s2t_fract48[47]};

  // rigt shift value
  // and appropriatelly corrected exponent
  wire s1o_exp10c_0 = !(|s1o_exp10c);
  wire [9:0] s2t_shr_of_neg_exp = 11'h401 - {1'b0,s1o_exp10c}; // 1024-v+1
  wire [9:0] s2t_exp10_p_carry = s1o_exp10c + s2t_carry10;
  //...
  wire [9:0] s2t_shrx;
  wire [9:0] s2t_exp10rx;
  assign {s2t_shrx,s2t_exp10rx} =
      // zero result case
    s1o_opc_0     ? {10'd0,10'd0} :
      // negative exponent sum
      //  (!) takes carry into account automatically
    s1o_exp10c[9] ? {s2t_shr_of_neg_exp,10'd1} :
      // zero exponent sum (denorm. result potentially)
      //  (!) takes carry into account automatically
    (!s1o_opc_0 & s1o_exp10c_0) ? 
                    {10'd1,10'd1} :
      // normal case at last
                    {s2t_carry10,s2t_exp10_p_carry};
  // max. right shift that makes sense i 26bits
  //  i.e. [47] moves to sticky position: ([21])
  // we use 6bits representation for shift value
  // to be aligned with shift left one
  wire [5:0] s2t_shr = (s2t_shrx > 10'd26) ? 6'd26 : s2t_shrx[5:0];

  // number of leading zeros 
  reg [5:0] s2t_nlz6;
  always @(s2t_fract48) begin
    casez(s2t_fract48)  // synopsys full_case parallel_case
      48'b1???????????????????????????????????????????????: s2t_nlz6 =   0; // shift right case
      48'b01??????????????????????????????????????????????: s2t_nlz6 =   0; // "1" is in place
      48'b001?????????????????????????????????????????????: s2t_nlz6 =   1;
      48'b0001????????????????????????????????????????????: s2t_nlz6 =   2;
      48'b00001???????????????????????????????????????????: s2t_nlz6 =   3;
      48'b000001??????????????????????????????????????????: s2t_nlz6 =   4;
      48'b0000001?????????????????????????????????????????: s2t_nlz6 =   5;
      48'b00000001????????????????????????????????????????: s2t_nlz6 =   6;
      48'b000000001???????????????????????????????????????: s2t_nlz6 =   7;
      48'b0000000001??????????????????????????????????????: s2t_nlz6 =   8;
      48'b00000000001?????????????????????????????????????: s2t_nlz6 =   9;
      48'b000000000001????????????????????????????????????: s2t_nlz6 =  10;
      48'b0000000000001???????????????????????????????????: s2t_nlz6 =  11;
      48'b00000000000001??????????????????????????????????: s2t_nlz6 =  12;
      48'b000000000000001?????????????????????????????????: s2t_nlz6 =  13;
      48'b0000000000000001????????????????????????????????: s2t_nlz6 =  14;
      48'b00000000000000001???????????????????????????????: s2t_nlz6 =  15;
      48'b000000000000000001??????????????????????????????: s2t_nlz6 =  16;
      48'b0000000000000000001?????????????????????????????: s2t_nlz6 =  17;
      48'b00000000000000000001????????????????????????????: s2t_nlz6 =  18;
      48'b000000000000000000001???????????????????????????: s2t_nlz6 =  19;
      48'b0000000000000000000001??????????????????????????: s2t_nlz6 =  20;
      48'b00000000000000000000001?????????????????????????: s2t_nlz6 =  21;
      48'b000000000000000000000001????????????????????????: s2t_nlz6 =  22;
      48'b0000000000000000000000001???????????????????????: s2t_nlz6 =  23;
      48'b00000000000000000000000001??????????????????????: s2t_nlz6 =  24;
      48'b000000000000000000000000001?????????????????????: s2t_nlz6 =  25;
      48'b0000000000000000000000000001????????????????????: s2t_nlz6 =  26;
      48'b00000000000000000000000000001???????????????????: s2t_nlz6 =  27;
      48'b000000000000000000000000000001??????????????????: s2t_nlz6 =  28;
      48'b0000000000000000000000000000001?????????????????: s2t_nlz6 =  29;
      48'b00000000000000000000000000000001????????????????: s2t_nlz6 =  30;
      48'b000000000000000000000000000000001???????????????: s2t_nlz6 =  31;
      48'b0000000000000000000000000000000001??????????????: s2t_nlz6 =  32;
      48'b00000000000000000000000000000000001?????????????: s2t_nlz6 =  33;
      48'b000000000000000000000000000000000001????????????: s2t_nlz6 =  34;
      48'b0000000000000000000000000000000000001???????????: s2t_nlz6 =  35;
      48'b00000000000000000000000000000000000001??????????: s2t_nlz6 =  36;
      48'b000000000000000000000000000000000000001?????????: s2t_nlz6 =  37;
      48'b0000000000000000000000000000000000000001????????: s2t_nlz6 =  38;
      48'b00000000000000000000000000000000000000001???????: s2t_nlz6 =  39;
      48'b000000000000000000000000000000000000000001??????: s2t_nlz6 =  40;
      48'b0000000000000000000000000000000000000000001?????: s2t_nlz6 =  41;
      48'b00000000000000000000000000000000000000000001????: s2t_nlz6 =  42;
      48'b000000000000000000000000000000000000000000001???: s2t_nlz6 =  43;
      48'b0000000000000000000000000000000000000000000001??: s2t_nlz6 =  44;
      48'b00000000000000000000000000000000000000000000001?: s2t_nlz6 =  45;
      48'b000000000000000000000000000000000000000000000001: s2t_nlz6 =  46;
      48'b000000000000000000000000000000000000000000000000: s2t_nlz6 =   0; // zero result
    endcase
  end // always
  //...
  wire [5:0] s2t_nlz6_m1 = s2t_nlz6 - 6'd1;
  wire [9:0] s2t_exp10c_mz = s1o_exp10c - {4'd0,s2t_nlz6};
  wire [9:0] s2t_exp10c_m1 = s1o_exp10c - 10'd1;
  // left shift amount and corrected exponent
  // if (nlz != 0) it means that (carry == 0)
  // so we can use exponent latched in previous state register
  wire [9:0] s2t_shlx;
  wire [9:0] s2t_exp10lx;
  assign {s2t_shlx,s2t_exp10lx} =
      // shift isn't needed (includes zero result)
    (!(|s2t_nlz6))           ? {10'd0,s1o_exp10c} :
      // normalization is possible
    (s1o_exp10c >  s2t_nlz6) ? {{4'd0,s2t_nlz6},s2t_exp10c_mz} :
      // denormalized cases
    (s1o_exp10c == s2t_nlz6) ? {{4'd0,s2t_nlz6_m1},10'd1} :
                               {s2t_exp10c_m1,10'd1};
  // actual size of shift value is 6 bits
  wire [5:0] s2t_shl = s2t_shlx[5:0];


  // stage #2 outputs
  //   input related
  reg s2o_inv, s2o_inf_i,
      s2o_snan_i, s2o_qnan_i, s2o_anan_i_sign;
  //   computation related
  reg        s2o_signc;
  reg [9:0]  s2o_exp10c;  
  reg [47:0] s2o_fract48;
  reg [5:0]  s2o_shr;
  reg [5:0]  s2o_shl;

  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s2o_inv         <= s1o_inv;
      s2o_inf_i       <= s1o_inf_i;
      s2o_snan_i      <= s1o_snan_i;
      s2o_qnan_i      <= s1o_qnan_i;
      s2o_anan_i_sign <= s1o_anan_i_sign;
        // computation related
        // right shif has got priority
      s2o_signc   <= s1o_signc;
      s2o_exp10c  <= (|s2t_shr) ? s2t_exp10rx : s2t_exp10lx;
      s2o_fract48 <= s2t_fract48;
      s2o_shr     <= s2t_shr;
      s2o_shl     <= s2t_shl;
    end // advance
  end // posedge clock

  // ready is special case
  reg s2o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      s2o_ready <= 0;
    else if(flush_i)
      s2o_ready <= 0;
    else if(adv_i)
      s2o_ready <= s1o_ready;
  end // posedge clock


  /* Stage #3: align */

  // shift fractional
  wire [47:0] s3t_fract48_sh;
  assign s3t_fract48_sh =
    (|s2o_shr) ? s2o_fract48 >> s2o_shr :
                 s2o_fract48 << s2o_shl;

  // sticky bit computation for right shift
  // max. right shift that makes sense i 26bits
  //  i.e. [47] moves to sticky position: ([21])
  reg s3t_sticky_shr;
  always @(s2o_shr or s2o_fract48) begin
    case(s2o_shr)
      6'd0   : s3t_sticky_shr = |s2o_fract48[21:0];
      6'd1   : s3t_sticky_shr = |s2o_fract48[22:0];
      6'd2   : s3t_sticky_shr = |s2o_fract48[23:0];
      6'd3   : s3t_sticky_shr = |s2o_fract48[24:0];
      6'd4   : s3t_sticky_shr = |s2o_fract48[25:0];
      6'd5   : s3t_sticky_shr = |s2o_fract48[26:0];
      6'd6   : s3t_sticky_shr = |s2o_fract48[27:0];
      6'd7   : s3t_sticky_shr = |s2o_fract48[28:0];
      6'd8   : s3t_sticky_shr = |s2o_fract48[29:0];
      6'd9   : s3t_sticky_shr = |s2o_fract48[30:0];
      6'd10  : s3t_sticky_shr = |s2o_fract48[31:0];
      6'd11  : s3t_sticky_shr = |s2o_fract48[32:0];
      6'd12  : s3t_sticky_shr = |s2o_fract48[33:0];
      6'd13  : s3t_sticky_shr = |s2o_fract48[34:0];
      6'd14  : s3t_sticky_shr = |s2o_fract48[35:0];
      6'd15  : s3t_sticky_shr = |s2o_fract48[36:0];
      6'd16  : s3t_sticky_shr = |s2o_fract48[37:0];
      6'd17  : s3t_sticky_shr = |s2o_fract48[38:0];
      6'd18  : s3t_sticky_shr = |s2o_fract48[39:0];
      6'd19  : s3t_sticky_shr = |s2o_fract48[40:0];
      6'd20  : s3t_sticky_shr = |s2o_fract48[41:0];
      6'd21  : s3t_sticky_shr = |s2o_fract48[42:0];
      6'd22  : s3t_sticky_shr = |s2o_fract48[43:0];
      6'd23  : s3t_sticky_shr = |s2o_fract48[44:0];
      6'd24  : s3t_sticky_shr = |s2o_fract48[45:0];
      6'd25  : s3t_sticky_shr = |s2o_fract48[46:0];
      default: s3t_sticky_shr = |s2o_fract48[47:0];
    endcase
  end // always

  // sticky bit computation for left shift
  reg s3t_sticky_shl;
  always @(s2o_shl or s2o_fract48) begin
    case(s2o_shl)
      6'd0   : s3t_sticky_shl = |s2o_fract48[21:0];
      6'd1   : s3t_sticky_shl = |s2o_fract48[20:0];
      6'd2   : s3t_sticky_shl = |s2o_fract48[19:0];
      6'd3   : s3t_sticky_shl = |s2o_fract48[18:0];
      6'd4   : s3t_sticky_shl = |s2o_fract48[17:0];
      6'd5   : s3t_sticky_shl = |s2o_fract48[16:0];
      6'd6   : s3t_sticky_shl = |s2o_fract48[15:0];
      6'd7   : s3t_sticky_shl = |s2o_fract48[14:0];
      6'd8   : s3t_sticky_shl = |s2o_fract48[13:0];
      6'd9   : s3t_sticky_shl = |s2o_fract48[12:0];
      6'd10  : s3t_sticky_shl = |s2o_fract48[11:0];
      6'd11  : s3t_sticky_shl = |s2o_fract48[10:0];
      6'd12  : s3t_sticky_shl = |s2o_fract48[ 9:0];
      6'd13  : s3t_sticky_shl = |s2o_fract48[ 8:0];
      6'd14  : s3t_sticky_shl = |s2o_fract48[ 7:0];
      6'd15  : s3t_sticky_shl = |s2o_fract48[ 6:0];
      6'd16  : s3t_sticky_shl = |s2o_fract48[ 5:0];
      6'd17  : s3t_sticky_shl = |s2o_fract48[ 4:0];
      6'd18  : s3t_sticky_shl = |s2o_fract48[ 3:0];
      6'd19  : s3t_sticky_shl = |s2o_fract48[ 2:0];
      6'd20  : s3t_sticky_shl = |s2o_fract48[ 1:0];
      6'd21  : s3t_sticky_shl =  s2o_fract48[   0];
      default: s3t_sticky_shl = 0;
    endcase
  end // always

  wire s3t_sticky = (|s2o_shr) ? s3t_sticky_shr : s3t_sticky_shl;


   // stage #3 outputs
    // input related
  reg s3o_inv, s3o_inf_i,
      s3o_snan_i, s3o_qnan_i, s3o_anan_i_sign;
      // computation related
  reg        s3o_signc;
  reg  [9:0] s3o_exp10c;
  reg [23:0] s3o_fract24c;
  reg  [1:0] s3o_rs;
  
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s3o_inv         <= s2o_inv;
      s3o_inf_i       <= s2o_inf_i;
      s3o_snan_i      <= s2o_snan_i;
      s3o_qnan_i      <= s2o_qnan_i;
      s3o_anan_i_sign <= s2o_anan_i_sign;
        // computation related
      s3o_signc    <= s2o_signc;
      s3o_exp10c   <= s2o_exp10c;
      s3o_fract24c <= s3t_fract48_sh[46:23];
      s3o_rs       <= {s3t_fract48_sh[22],s3t_sticky};
    end // advance
  end // posedge clock

  // ready is special case
  reg s3o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      s3o_ready  <= 0;
    else if(flush_i)
      s3o_ready  <= 0;
    else if(adv_i)
      s3o_ready <= s2o_ready;
  end // posedge clock


  /* Stage #4: rounding and output */

  // rounding mode isn't require pipelinization
  wire rm_nearest = (rmode_i==2'b00);
  wire rm_to_zero = (rmode_i==2'b01);
  wire rm_to_infp = (rmode_i==2'b10);
  wire rm_to_infm = (rmode_i==2'b11);

  wire s4t_g    = s3o_fract24c[0];
  wire s4t_r    = s3o_rs[1];
  wire s4t_s    = s3o_rs[0];
  wire s4t_lost = s4t_r | s4t_s;

  wire s4t_rnd_up = (rm_nearest & s4t_r & s4t_s) |
                    (rm_nearest & s4t_g & s4t_r & !s4t_s) |
                    (rm_to_infp & !s3o_signc & s4t_lost) |
                    (rm_to_infm &  s3o_signc & s4t_lost);

  wire [24:0] s4t_fract25c = {1'b0,s3o_fract24c} + {24'd0,s4t_rnd_up};

  wire s4t_shr = s4t_fract25c[24];

  wire [9:0]  s4t_exp10c   = s3o_exp10c + {9'd0,s4t_shr};
  wire [23:0] s4t_fract24c = s4t_shr ? s4t_fract25c[24:1] :
                                       s4t_fract25c[23:0];

   // potentially denormalized
  wire s4t_fract24c_dn = !s4t_fract24c[23];
   // potentially zero
  wire s4t_fract24c_00 = !(|s4t_fract24c);

   // Generate result and flags
  wire s4t_ine, s4t_ovf, s4t_inf, s4t_unf, s4t_zer;
  wire [31:0] s4t_opc;
  assign {s4t_opc,s4t_ine,s4t_ovf,s4t_inf,s4t_unf,s4t_zer} =
    // qnan output
    (s3o_snan_i | s3o_qnan_i) ? // ine  ovf  inf  unf  zer
      {{s3o_anan_i_sign,QNAN},    1'b0,1'b0,1'b0,1'b0,1'b0} :
    // snan output
    s3o_inv ?         // ine  ovf  inf  unf  zer
      {{s3o_signc,SNAN},1'b0,1'b0,1'b0,1'b0,1'b0} :
    // overflow and infinity
    ((s4t_exp10c > 10'd254) | s3o_inf_i) ? // ine        ovf  inf  unf  zer
      {{s3o_signc,INF}, (s4t_lost | (!s3o_inf_i)),!s3o_inf_i,1'b1,1'b0,1'b0} :
    // zero and underflow
    (s4t_fract24c_dn | s4t_fract24c_00) ?    // ine  ovf  inf               unf               zer
      {{s3o_signc,8'd0,s4t_fract24c[22:0]},s4t_lost,1'b0,1'b0,(s4t_fract24c_00 & s4t_lost),s4t_fract24c_00} :
    // normal result                                   ine  ovf  inf  unf  zer
    {s3o_signc,s4t_exp10c[7:0],s4t_fract24c[22:0],s4t_lost,1'b0,1'b0,1'b0,1'b0};

   // Output Register
  always @(posedge clk) begin
    if(adv_i) begin
      opc_o  <= s4t_opc;
      ine_o  <= s4t_ine;
      inv_o  <= s3o_inv | s3o_snan_i;
      ovf_o  <= s4t_ovf;
      inf_o  <= s4t_inf;
      unf_o  <= s4t_unf;
      zer_o  <= s4t_zer;
    end
  end // posedge clock

  // ready is special case
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      ready_o <= 0;
    else if(flush_i)
      ready_o <= 0;
    else if(adv_i)
      ready_o <= s3o_ready;
  end // posedge clock
  
endmodule // pfpu32_mul
