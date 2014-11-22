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
   output reg        inv_o,    // inf-inf -> invalid flag & qnan result
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

  /* Stage #1: pre addition / substruction align */

    // detection of some exceptions
    //   inf - inf -> invalid operation; snan output
  wire s1t_inv = infa_i & infb_i &
                 (signa_i ^ (is_sub_i ^ signb_i));
    //   inf input
  wire s1t_inf_i = infa_i | infb_i;

    // select larger operand
    //  (substruction always peform (larger-smaller))  
  wire s1t_agtb = (exp10a_i > exp10b_i) |
    ((exp10a_i == exp10b_i) & (fract24a_i > fract24b_i));

    // signums for calculation
  wire s1t_calc_signa = signa_i & (!zeroa_i); // non-zero
  wire s1t_calc_signb = (signb_i ^ is_sub_i) & (!zerob_i); // non-zero

    // not shifted operand and its signum
  wire s1t_sign_nsh;
  wire [23:0] s1t_fract24_nsh;
  assign {s1t_sign_nsh,s1t_fract24_nsh} = s1t_agtb ?
    {s1t_calc_signa,fract24a_i} :
    {s1t_calc_signb,fract24b_i};

    // operand and its signum for right shift
    //  + two bits for further rounding and shifts
  wire s1t_sign_fsh;
  wire [25:0] s1t_fract26_fsh;
  assign {s1t_sign_fsh,s1t_fract26_fsh} = s1t_agtb ?
    {s1t_calc_signb,{(fract24b_i & {24{!s1t_inf_i}}),2'd0}} :
    {s1t_calc_signa,{(fract24a_i & {24{!s1t_inf_i}}),2'd0}};


    // shift amount
    //  (max 26 bits shift makes sense:
    //    hidden '1' achieves sticky area)
  wire [9:0] s1t_exp_diff =
    s1t_inf_i ? 10'd255 :
    s1t_agtb  ? (exp10a_i - exp10b_i) :
                (exp10b_i - exp10a_i);

  wire [4:0] s1t_shr = (s1t_exp_diff > 10'd26) ?
                       5'd26 : s1t_exp_diff[4:0];


  // stage #1 outputs
  reg s1o_inv, s1o_inf_i,
      s1o_snan_i, s1o_qnan_i, s1o_anan_i_sign;
  reg        s1o_nsh_minus_shr; // perform (non_shifted - right_shifted)
  reg        s1o_signc; // signum of result
  reg [9:0]  s1o_exp10c;
  reg [23:0] s1o_fract24_nsh; // not shifted,
  reg [25:0] s1o_fract26_shr; // right shifted
    // rounding support
  reg s1o_sticky; 

  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s1o_inv         <= s1t_inv;
      s1o_inf_i       <= s1t_inf_i;
      s1o_snan_i      <= snan_i;
      s1o_qnan_i      <= qnan_i;
      s1o_anan_i_sign <= anan_sign_i;
        // operation type for non-shifted and shifted parts
      s1o_nsh_minus_shr <= s1t_sign_nsh ^ s1t_sign_fsh; // not equal
        //  signum of result
      s1o_signc <= s1t_sign_nsh;
        // exponent of result (estimation on the stage)
      s1o_exp10c <= s1t_agtb ? exp10a_i : exp10b_i;
        // not shifted operand
      s1o_fract24_nsh <= s1t_fract24_nsh;
        // right shifted operand
      s1o_fract26_shr <= s1t_fract26_fsh >> s1t_shr;
        // detection of obvious precision lost
        // (take into account the out of adder bits) 
      case(s1t_shr)
        5'd0, 5'd1, 5'd2 : s1o_sticky <= 1'b0; // two added zero bits
        5'd3 : s1o_sticky <= s1t_fract26_fsh[2];
        5'd4 : s1o_sticky <= |s1t_fract26_fsh[3:2];
        5'd5 : s1o_sticky <= |s1t_fract26_fsh[4:2];
        5'd6 : s1o_sticky <= |s1t_fract26_fsh[5:2];
        5'd7 : s1o_sticky <= |s1t_fract26_fsh[6:2];
        5'd8 : s1o_sticky <= |s1t_fract26_fsh[7:2];
        5'd9 : s1o_sticky <= |s1t_fract26_fsh[8:2];
        5'd10: s1o_sticky <= |s1t_fract26_fsh[9:2];
        5'd11: s1o_sticky <= |s1t_fract26_fsh[10:2];
        5'd12: s1o_sticky <= |s1t_fract26_fsh[11:2];
        5'd13: s1o_sticky <= |s1t_fract26_fsh[12:2];
        5'd14: s1o_sticky <= |s1t_fract26_fsh[13:2];
        5'd15: s1o_sticky <= |s1t_fract26_fsh[14:2];
        5'd16: s1o_sticky <= |s1t_fract26_fsh[15:2];
        5'd17: s1o_sticky <= |s1t_fract26_fsh[16:2];
        5'd18: s1o_sticky <= |s1t_fract26_fsh[17:2];
        5'd19: s1o_sticky <= |s1t_fract26_fsh[18:2];
        5'd20: s1o_sticky <= |s1t_fract26_fsh[19:2];
        5'd21: s1o_sticky <= |s1t_fract26_fsh[20:2];
        5'd22: s1o_sticky <= |s1t_fract26_fsh[21:2];
        5'd23: s1o_sticky <= |s1t_fract26_fsh[22:2];
        5'd24: s1o_sticky <= |s1t_fract26_fsh[23:2];
        5'd25: s1o_sticky <= |s1t_fract26_fsh[24:2];
        default: s1o_sticky <= |s1t_fract26_fsh[25:2];
      endcase
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


  /* Stage #2 */

    // add/sub of non-shifted and shifted operands
  wire [27:0] s2t_diff28  = 
           {1'b0,s1o_fract24_nsh,3'd0} - {1'b0,s1o_fract26_shr,s1o_sticky};
  wire [26:0] s2t_fract27 = s1o_nsh_minus_shr ?
                            s2t_diff28[27:1]:
                            ({1'b0,s1o_fract24_nsh,2'd0} + {1'b0,s1o_fract26_shr});

    // pre-round align (1st step of normalization)
      // one more right shift ?
  wire s2t_shr = s2t_fract27[26];

  // stage #2 outputs
    // input related
  reg s2o_inv, s2o_inf_i,
      s2o_snan_i, s2o_qnan_i, s2o_anan_i_sign;
    // computation related
  reg        s2o_signc;
  reg [9:0]  s2o_exp10c;
  reg [25:0] s2o_fract26c;
  reg        s2o_sticky;
  reg [4:0]  s2o_nlz;

  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s2o_inv         <= s1o_inv;
      s2o_inf_i       <= s1o_inf_i;
      s2o_snan_i      <= s1o_snan_i;
      s2o_qnan_i      <= s1o_qnan_i;
      s2o_anan_i_sign <= s1o_anan_i_sign;
        // computation related
      s2o_signc    <= s1o_signc;
      s2o_exp10c   <= s2t_shr ? (s1o_exp10c + 10'd1) : s1o_exp10c;
      s2o_fract26c <= s2t_shr ? s2t_fract27[26:1] : s2t_fract27[25:0];
      s2o_sticky   <= (s2t_shr & s2t_fract27[0]) | s1o_sticky;
        // for possible left shift
        // [26] bit is right shift flag
      casez(s2t_fract27)
        27'b1??????????????????????????: s2o_nlz <=  0; // [26] bit: shift right
        27'b01?????????????????????????: s2o_nlz <=  0; // 1 is in place
        27'b001????????????????????????: s2o_nlz <=  1;
        27'b0001???????????????????????: s2o_nlz <=  2;
        27'b00001??????????????????????: s2o_nlz <=  3;
        27'b000001?????????????????????: s2o_nlz <=  4;
        27'b0000001????????????????????: s2o_nlz <=  5;
        27'b00000001???????????????????: s2o_nlz <=  6;
        27'b000000001??????????????????: s2o_nlz <=  7;
        27'b0000000001?????????????????: s2o_nlz <=  8;
        27'b00000000001????????????????: s2o_nlz <=  9;
        27'b000000000001???????????????: s2o_nlz <= 10;
        27'b0000000000001??????????????: s2o_nlz <= 11;
        27'b00000000000001?????????????: s2o_nlz <= 12;
        27'b000000000000001????????????: s2o_nlz <= 13;
        27'b0000000000000001???????????: s2o_nlz <= 14;
        27'b00000000000000001??????????: s2o_nlz <= 15;
        27'b000000000000000001?????????: s2o_nlz <= 16;
        27'b0000000000000000001????????: s2o_nlz <= 17;
        27'b00000000000000000001???????: s2o_nlz <= 18;
        27'b000000000000000000001??????: s2o_nlz <= 19;
        27'b0000000000000000000001?????: s2o_nlz <= 20;
        27'b00000000000000000000001????: s2o_nlz <= 21;
        27'b000000000000000000000001???: s2o_nlz <= 22;
        27'b0000000000000000000000001??: s2o_nlz <= 23;
        27'b00000000000000000000000001?: s2o_nlz <= 24;
        27'b000000000000000000000000001: s2o_nlz <= 25;
        27'b000000000000000000000000000: s2o_nlz <=  0; // zero result
      endcase
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


  /* Stage #3: align */

  // left shift amount and corrected exponent
  wire [4:0] s3t_nlz_m1 = (s2o_nlz - 5'd1);
  wire [9:0] s3t_exp10c_m1 = s2o_exp10c - 10'd1;
  wire [9:0] s3t_exp10c_mz = s2o_exp10c - {5'd0,s2o_nlz};
  wire [4:0] s3t_shl;
  wire [9:0] s3t_exp10c;
  assign {s3t_shl,s3t_exp10c} =
      // shift isn't needed or impossible
    (!(|s2o_nlz) | (s2o_exp10c == 10'd1)) ?
                              {5'd0,s2o_exp10c} :
      // normalization is possible
    (s2o_exp10c >  s2o_nlz) ? {s2o_nlz,s3t_exp10c_mz} :
      // denormalized cases
    (s2o_exp10c == s2o_nlz) ? {s3t_nlz_m1,10'd1} :
                              {s3t_exp10c_m1[4:0],10'd1};

  wire [25:0] s3t_fract26c = s2o_fract26c << s3t_shl;

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
      s3o_exp10c   <= s3t_exp10c;
      s3o_fract24c <= s3t_fract26c[25:2];
      s3o_rs       <= {s3t_fract26c[1], s3t_fract26c[0] | s2o_sticky};
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

endmodule // pfpu32_addsub
