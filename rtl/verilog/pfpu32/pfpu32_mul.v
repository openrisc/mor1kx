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
   input             signa_i,  // input 'a' related values
   input       [9:0] exp10a_i,
   input      [23:0] fract24a_i,
   input             infa_i,
   input             zeroa_i,
   input             dna_i,    // 'a' is denormalized
   input             signb_i,  // input 'b' related values
   input       [9:0] exp10b_i,
   input      [23:0] fract24b_i,
   input             infb_i,
   input             zerob_i,
   input             dnb_i,    // 'b' is denormalized
   input             snan_i,   // 'a'/'b' related
   input             qnan_i,
   input             anan_sign_i,
   output reg        mul_rdy_o,       // mul is ready
   output reg        mul_sign_o,      // mul signum
   output reg  [9:0] mul_exp10_o,     // mul exponent
   output reg [23:0] mul_fract24_o,   // mul fractional
   output reg  [1:0] mul_rs_o,        // mul round & sticky bits
   output reg        mul_inv_o,       // mul invalid operation flag
   output reg        mul_inf_o,       // mul infinity output reg
   output reg        mul_snan_o,      // mul signaling NaN output reg
   output reg        mul_qnan_o,      // mul quiet NaN output reg
   output reg        mul_anan_sign_o  // mul signum for output nan
);

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

    // input is normalized
  wire s1t_ab_norm = ~(dna_i | dnb_i);

  // count leading zeros
  reg [4:0] s1t_nlza;
  always @(fract24a_i)
    casez(fract24a_i) // synopsys full_case parallel_case
      24'b1???????????????????????: s1t_nlza =  0;
      24'b01??????????????????????: s1t_nlza =  1;
      24'b001?????????????????????: s1t_nlza =  2;
      24'b0001????????????????????: s1t_nlza =  3;
      24'b00001???????????????????: s1t_nlza =  4;
      24'b000001??????????????????: s1t_nlza =  5;
      24'b0000001?????????????????: s1t_nlza =  6;
      24'b00000001????????????????: s1t_nlza =  7;
      24'b000000001???????????????: s1t_nlza =  8;
      24'b0000000001??????????????: s1t_nlza =  9;
      24'b00000000001?????????????: s1t_nlza = 10;
      24'b000000000001????????????: s1t_nlza = 11;
      24'b0000000000001???????????: s1t_nlza = 12;
      24'b00000000000001??????????: s1t_nlza = 13;
      24'b000000000000001?????????: s1t_nlza = 14;
      24'b0000000000000001????????: s1t_nlza = 15;
      24'b00000000000000001???????: s1t_nlza = 16;
      24'b000000000000000001??????: s1t_nlza = 17;
      24'b0000000000000000001?????: s1t_nlza = 18;
      24'b00000000000000000001????: s1t_nlza = 19;
      24'b000000000000000000001???: s1t_nlza = 20;
      24'b0000000000000000000001??: s1t_nlza = 21;
      24'b00000000000000000000001?: s1t_nlza = 22;
      24'b000000000000000000000001: s1t_nlza = 23;
      24'b000000000000000000000000: s1t_nlza =  0; // zero rezult
    endcase

  // count leading zeros
  reg [4:0] s1t_nlzb;
  always @(fract24b_i)
    casez(fract24b_i) // synopsys full_case parallel_case
      24'b1???????????????????????: s1t_nlzb =  0;
      24'b01??????????????????????: s1t_nlzb =  1;
      24'b001?????????????????????: s1t_nlzb =  2;
      24'b0001????????????????????: s1t_nlzb =  3;
      24'b00001???????????????????: s1t_nlzb =  4;
      24'b000001??????????????????: s1t_nlzb =  5;
      24'b0000001?????????????????: s1t_nlzb =  6;
      24'b00000001????????????????: s1t_nlzb =  7;
      24'b000000001???????????????: s1t_nlzb =  8;
      24'b0000000001??????????????: s1t_nlzb =  9;
      24'b00000000001?????????????: s1t_nlzb = 10;
      24'b000000000001????????????: s1t_nlzb = 11;
      24'b0000000000001???????????: s1t_nlzb = 12;
      24'b00000000000001??????????: s1t_nlzb = 13;
      24'b000000000000001?????????: s1t_nlzb = 14;
      24'b0000000000000001????????: s1t_nlzb = 15;
      24'b00000000000000001???????: s1t_nlzb = 16;
      24'b000000000000000001??????: s1t_nlzb = 17;
      24'b0000000000000000001?????: s1t_nlzb = 18;
      24'b00000000000000000001????: s1t_nlzb = 19;
      24'b000000000000000000001???: s1t_nlzb = 20;
      24'b0000000000000000000001??: s1t_nlzb = 21;
      24'b00000000000000000000001?: s1t_nlzb = 22;
      24'b000000000000000000000001: s1t_nlzb = 23;
      24'b000000000000000000000000: s1t_nlzb =  0; // zero result
    endcase


  // side back shifters to normalize inputs
  reg [23:0] s11o_fract24a;
  reg  [4:0] s11o_shla;
  reg [23:0] s11o_fract24b;
  reg  [4:0] s11o_shlb;
  // registering
  always @(posedge clk) begin
    s11o_fract24a <= fract24a_i;
    s11o_shla     <= s1t_nlza;
    s11o_fract24b <= fract24b_i;
    s11o_shlb     <= s1t_nlzb;
  end

  // route ready through side back
  reg s11o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      s11o_ready <= 0;
    else if(flush_i)
      s11o_ready <= 0;
    else if(adv_i)
      s11o_ready <= start_i & (~s1t_ab_norm);
  end // posedge clock


  // left-shift the dividend and divisor
  wire [23:0] s12t_fract24a_sh = s11o_fract24a << s11o_shla;
  wire [23:0] s12t_fract24b_sh = s11o_fract24b << s11o_shlb;


  // stage #1 outputs
  //   input related
  reg s1o_inv, s1o_inf_i,
      s1o_snan_i, s1o_qnan_i, s1o_anan_i_sign;
  //   computation related
  reg        s1o_opc_0;
  reg        s1o_signc;
  reg [9:0]  s1o_exp10c;
  reg [31:0] s1o_fract32a;
  reg [31:0] s1o_fract32b;
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
      s1o_opc_0    <= s1t_opc_0;
      s1o_signc    <= signa_i ^ signb_i;
      s1o_exp10c   <= {10{!s1t_opc_0}} &
                      ( s1t_ab_norm ? (exp10a_i + exp10b_i - 10'd127) :
                                      (exp10a_i + exp10b_i - {5'd0,s11o_shla} - {5'd0,s11o_shlb} - 10'd127) );
      s1o_fract32a <= {(s1t_ab_norm ? fract24a_i : s12t_fract24a_sh), 8'd0};
      s1o_fract32b <= {(s1t_ab_norm ? fract24b_i : s12t_fract24b_sh), 8'd0};
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
      s1o_ready <= s11o_ready | (start_i & s1t_ab_norm);
  end // posedge clock


  /* Stage #2: 1st part of multiplier */


  // computation related fractionals
  //  insert leading zeros to signal unsigned values
  //  for potential usage DSP blocks of a FPGA
  wire [16:0] m1t_fract17_al = {1'b0, s1o_fract32a[15: 0]};
  wire [16:0] m1t_fract17_ah = {1'b0, s1o_fract32a[31:16]};
  wire [16:0] m1t_fract17_bl = {1'b0, s1o_fract32b[15: 0]};
  wire [16:0] m1t_fract17_bh = {1'b0, s1o_fract32b[31:16]};

  // partial products: m1o==s2o
  reg [33:0] m1o_fract34_albl;
  reg [33:0] m1o_fract34_albh;
  reg [33:0] m1o_fract34_ahbl;
  reg [33:0] m1o_fract34_ahbh;
  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
      m1o_fract34_albl <= m1t_fract17_al * m1t_fract17_bl;
      m1o_fract34_albh <= m1t_fract17_al * m1t_fract17_bh;
      m1o_fract34_ahbl <= m1t_fract17_ah * m1t_fract17_bl;
      m1o_fract34_ahbh <= m1t_fract17_ah * m1t_fract17_bh;
    end // advance pipe
  end // posedge clock

  // stage #2 outputs
  //   input related
  reg s2o_inv, s2o_inf_i,
      s2o_snan_i, s2o_qnan_i, s2o_anan_i_sign;
  //   computation related
  reg        s2o_opc_0;
  reg        s2o_signc;
  reg [9:0]  s2o_exp10c;
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
      s2o_opc_0  <= s1o_opc_0;
      s2o_signc  <= s1o_signc;
      s2o_exp10c <= s1o_exp10c;
    end // advance pipe
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


  /* Stage #3: 2nd part of multiplier */


  wire [63:0] m2t_fract64;
  assign m2t_fract64 = {m1o_fract34_ahbh[31:0],  32'd0} +
                       {14'd0, m1o_fract34_ahbl, 16'd0} +
                       {14'd0, m1o_fract34_albh, 16'd0} +
                       {32'd0,  m1o_fract34_albl[31:0]};

  // significant part of product: m2o==s3o
  reg [27:0] m2o_fract28;
  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
      m2o_fract28 <= {m2t_fract64[63:37],|m2t_fract64[36:0]};
    end // advance pipe
  end // posedge clock

  // left shift impossible as input operands are normalised: [1,2)

  // rigt shift value
  // and appropriatelly corrected exponent
  wire s2o_exp10c_0 = !(|s2o_exp10c);
  wire [9:0] s3t_shr_of_neg_exp = 11'h401 - {1'b0,s2o_exp10c}; // 1024-v+1
  // variants:
  wire [9:0] s3t_shrx;
  wire [9:0] s3t_exp10rx;
  assign {s3t_shrx,s3t_exp10rx} =
      // zero result case
    s2o_opc_0     ? {10'd0,10'd0} :
      // negative exponent sum
      //  (!) takes 1x.xx case into account automatically
    s2o_exp10c[9] ? {s3t_shr_of_neg_exp,10'd1} :
      // zero exponent sum (denorm. result potentially)
      //  (!) takes 1x.xx case into account automatically
    (!s2o_opc_0 & s2o_exp10c_0) ? 
                    {10'd1,10'd1} :
      // normal case at last
      //  (!) 1x.xx case is processed in next stage
                    {10'd0,s2o_exp10c};
  // max. right shift that makes sense is 27bits
  //  i.e. [27] moves to sticky position: [0]
  wire [4:0] s3t_shr = (s3t_shrx > 10'd27) ? 5'd27 : s3t_shrx[4:0];

  // stage #3 outputs
  //   input related
  reg s3o_inv, s3o_inf_i,
      s3o_snan_i, s3o_qnan_i, s3o_anan_i_sign;
  //   computation related
  reg        s3o_signc;
  reg [4:0]  s3o_shr;
  reg [9:0]  s3o_exp10;
  reg [9:0]  s3o_exp10p1; // +1 for align of possible 1x.xx fractional
  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s3o_inv         <= s2o_inv;
      s3o_inf_i       <= s2o_inf_i;
      s3o_snan_i      <= s2o_snan_i;
      s3o_qnan_i      <= s2o_qnan_i;
      s3o_anan_i_sign <= s2o_anan_i_sign;
        // computation related
      s3o_signc   <= s2o_signc;
      s3o_shr     <= s3t_shr;
      s3o_exp10   <= s3t_exp10rx;
      s3o_exp10p1 <= s2o_exp10c + 10'd1; // +1 for possible normalization of 2.xx fractional
    end // advance pipe
  end // posedge clock

  // ready is special case
  reg s3o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      s3o_ready <= 0;
    else if(flush_i)
      s3o_ready <= 0;
    else if(adv_i)
      s3o_ready <= s2o_ready;
  end // posedge clock


  /* Stage #4: right align and output */


  // final calculation of right shift value and intermediate exponent
  wire [4:0] s4t_shr;
  wire [9:0] s4t_exp10;
  assign {s4t_shr,s4t_exp10} =
    (|s3o_shr)      ? {s3o_shr,s3o_exp10} : // denormalized cases
    m2o_fract28[27] ? {5'd1,s3o_exp10p1}  : // 1x.xx case
                      {5'd0,s3o_exp10};     // regular

  // align
  wire [27:0] s4t_fract28sh = m2o_fract28 >> s4t_shr;

  // update sticky  bit
  reg s4r_sticky;
  always @(m2o_fract28 or s4t_shr) begin
    case (s4t_shr)
      5'd0   : s4r_sticky = |m2o_fract28[ 1:0];
      5'd1   : s4r_sticky = |m2o_fract28[ 2:0];
      5'd2   : s4r_sticky = |m2o_fract28[ 3:0];
      5'd3   : s4r_sticky = |m2o_fract28[ 4:0];
      5'd4   : s4r_sticky = |m2o_fract28[ 5:0];
      5'd5   : s4r_sticky = |m2o_fract28[ 6:0];
      5'd6   : s4r_sticky = |m2o_fract28[ 7:0];
      5'd7   : s4r_sticky = |m2o_fract28[ 8:0];
      5'd8   : s4r_sticky = |m2o_fract28[ 9:0];
      5'd9   : s4r_sticky = |m2o_fract28[10:0];
      5'd10  : s4r_sticky = |m2o_fract28[11:0];
      5'd11  : s4r_sticky = |m2o_fract28[12:0];
      5'd12  : s4r_sticky = |m2o_fract28[13:0];
      5'd13  : s4r_sticky = |m2o_fract28[14:0];
      5'd14  : s4r_sticky = |m2o_fract28[15:0];
      5'd15  : s4r_sticky = |m2o_fract28[16:0];
      5'd16  : s4r_sticky = |m2o_fract28[17:0];
      5'd17  : s4r_sticky = |m2o_fract28[18:0];
      5'd18  : s4r_sticky = |m2o_fract28[19:0];
      5'd19  : s4r_sticky = |m2o_fract28[20:0];
      5'd20  : s4r_sticky = |m2o_fract28[21:0];
      5'd21  : s4r_sticky = |m2o_fract28[22:0];
      5'd22  : s4r_sticky = |m2o_fract28[23:0];
      5'd23  : s4r_sticky = |m2o_fract28[24:0];
      5'd24  : s4r_sticky = |m2o_fract28[25:0];
      5'd25  : s4r_sticky = |m2o_fract28[26:0];
      default: s4r_sticky = |m2o_fract28[27:0];
    endcase
  end // always

  // registering output
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      mul_inv_o       <= s3o_inv;
      mul_inf_o       <= s3o_inf_i;
      mul_snan_o      <= s3o_snan_i;
      mul_qnan_o      <= s3o_qnan_i;
      mul_anan_sign_o <= s3o_anan_i_sign;
        // computation related
      mul_sign_o    <= s3o_signc;
      mul_exp10_o   <= s4t_exp10;
      mul_fract24_o <= s4t_fract28sh[26:3];
      mul_rs_o      <= {s4t_fract28sh[2],s4r_sticky};
    end // advance
  end // posedge clock

  // ready is special case
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      mul_rdy_o <= 0;
    else if(flush_i)
      mul_rdy_o <= 0;
    else if(adv_i)
      mul_rdy_o <= s3o_ready;
  end // posedge clock

endmodule // pfpu32_mul
