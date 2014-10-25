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
  localparam EXP_WIDTH = 8;
  localparam FRAC_WIDTH = 23;

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
  wire [EXP_WIDTH-1:0]  s1t_expa = opa_i[30:23];
  wire [EXP_WIDTH-1:0]  s1t_expb = opb_i[30:23];
  wire [FRAC_WIDTH-1:0] s1t_fracta = opa_i[22:0];
  wire [FRAC_WIDTH-1:0] s1t_fractb = opb_i[22:0];

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
    // result is zero
  wire s1t_opa_0 = !(|opa_i[30:0]);
  wire s1t_opb_0 = !(|opb_i[30:0]);

   // restore hidden "1"
  wire [FRAC_WIDTH:0] s1t_fracta_24 = {!s1t_opa_dn,s1t_fracta};
  wire [FRAC_WIDTH:0] s1t_fractb_24 = {!s1t_opb_dn,s1t_fractb};

  // count leading zeros
  reg [5:0] s1t_dvd_zeros;
  always @(s1t_fracta_24)
    casez(s1t_fracta_24) // synopsys full_case parallel_case
      24'b1???????????????????????: s1t_dvd_zeros = 0;
      24'b01??????????????????????: s1t_dvd_zeros = 1;
      24'b001?????????????????????: s1t_dvd_zeros = 2;
      24'b0001????????????????????: s1t_dvd_zeros = 3;
      24'b00001???????????????????: s1t_dvd_zeros = 4;
      24'b000001??????????????????: s1t_dvd_zeros = 5;
      24'b0000001?????????????????: s1t_dvd_zeros = 6;
      24'b00000001????????????????: s1t_dvd_zeros = 7;
      24'b000000001???????????????: s1t_dvd_zeros = 8;
      24'b0000000001??????????????: s1t_dvd_zeros = 9;
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
      24'b000000000000000000000000: s1t_dvd_zeros = 24;
    endcase

  // count leading zeros
  reg [5:0] s1t_div_zeros;
  always @(s1t_fractb_24)
    casez(s1t_fractb_24) // synopsys full_case parallel_case
      24'b1???????????????????????: s1t_div_zeros = 0;
      24'b01??????????????????????: s1t_div_zeros = 1;
      24'b001?????????????????????: s1t_div_zeros = 2;
      24'b0001????????????????????: s1t_div_zeros = 3;
      24'b00001???????????????????: s1t_div_zeros = 4;
      24'b000001??????????????????: s1t_div_zeros = 5;
      24'b0000001?????????????????: s1t_div_zeros = 6;
      24'b00000001????????????????: s1t_div_zeros = 7;
      24'b000000001???????????????: s1t_div_zeros = 8;
      24'b0000000001??????????????: s1t_div_zeros = 9;
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
      24'b000000000000000000000000: s1t_div_zeros = 24;
    endcase

  // left-shift the dividend and divisor
  wire [FRAC_WIDTH:0] s1t_fracta_lshift_intermediate;
  wire [FRAC_WIDTH:0] s1t_fractb_lshift_intermediate;
  assign s1t_fracta_lshift_intermediate = s1t_fracta_24 << s1t_dvd_zeros;
  assign s1t_fractb_lshift_intermediate = s1t_fractb_24 << s1t_div_zeros;

  wire [EXP_WIDTH+1:0] s1t_expa_10 = {2'd0,s1t_expa} + {9'd0,s1t_opa_dn};
  wire [EXP_WIDTH+1:0] s1t_expb_10 = {2'd0,s1t_expb} + {9'd0,s1t_opb_dn};

  // stage #1 outputs
  //   input related
  reg s1o_infa, s1o_infb,
      s1o_snan_a, s1o_qnan_a, s1o_snan_b, s1o_qnan_b;
  reg s1o_opa_0, s1o_opb_0;
  //   computation related
  reg s1o_sign;
  reg [EXP_WIDTH+1:0] s1o_exp10;
  reg [2*(FRAC_WIDTH+2)-1:0] s1o_dvdnd_50;
  reg [FRAC_WIDTH+3:0]       s1o_dvsor_27;

  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s1o_infa  <= s1t_infa;
      s1o_infb  <= s1t_infb;
      s1o_snan_a <= s1t_snan_a;
      s1o_qnan_a <= s1t_qnan_a;
      s1o_snan_b <= s1t_snan_b;
      s1o_qnan_b <= s1t_qnan_b;
      s1o_opa_0 <= s1t_opa_0;
      s1o_opb_0 <= s1t_opb_0;
        // computation related
      s1o_sign <= s1t_signa ^ s1t_signb;
      s1o_exp10 <= s1t_expa_10 - s1t_expb_10 + 10'b0001111111 -
                  {4'd0,s1t_dvd_zeros} + {4'd0,s1t_div_zeros};
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
      s2t_ready <= 0;
    end
    else if (s1o_ready & adv_i) begin
      s2t_state <= STATE_BUSY;
      s2t_count <= 26;
    end
    else if ((!(|s2t_count) & s2t_state==STATE_BUSY) & adv_i) begin
      s2t_state <= STATE_WAITING;
      s2t_ready <= 1;
      s2t_count <=26;
    end
    else if ((s2t_state==STATE_BUSY) & adv_i)
      s2t_count <= s2t_count - 1;
    else if(adv_i) begin
      s2t_state <= STATE_WAITING;
      s2t_ready <= 0;
    end
  end // posedge clock

  reg [FRAC_WIDTH+3:0]   s2t_qutnt;
  reg [FRAC_WIDTH+3:0]   s2t_rmndr;
  reg [FRAC_WIDTH+3:0]   s2t_dvd;

  wire [26:0] v2t_div;
  wire [26:0] v2t_div_minus_s1o_dvsor_27;

  assign v2t_div = (s2t_count==26) ? {3'd0,s1o_dvdnd_50[49:26]} : s2t_dvd;
  assign v2t_div_minus_s1o_dvsor_27 = v2t_div - s1o_dvsor_27;

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i) begin
      s2t_qutnt <= 0;
      s2t_rmndr <= 0;
    end
    else if (s1o_ready & adv_i) begin
      s2t_qutnt <= 0;
      s2t_rmndr <= 0;
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
  reg s2o_sign;
  reg [EXP_WIDTH+1:0] s2o_exp10;
  reg [FRAC_WIDTH+3:0] s2o_qutnt;
  reg s2o_lost;

  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s2o_infa  <= s1o_infa;
      s2o_infb  <= s1o_infb;
      s2o_snan_a <= s1o_snan_a;
      s2o_qnan_a <= s1o_qnan_a;
      s2o_snan_b <= s1o_snan_b;
      s2o_qnan_b <= s1o_qnan_b;
      s2o_opa_0 <= s1o_opa_0;
      s2o_opb_0 <= s1o_opb_0;
        // computation related
      s2o_sign <= s1o_sign;
      s2o_exp10 <= s1o_exp10;
      s2o_qutnt <= s2t_qutnt;
      s2o_lost <= |s2t_rmndr;
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


  /*
    Stages #3, #4, #5 and #6 : post multiplier normalization
  */

  // qutnt_i
  // 26 25                    3
  // |  |                     |
  // h  fffffffffffffffffffffff grs

  /* Stage #3 */
  // figure out the exponent and how far the fraction has to be shifted
  // right or left

   wire s3t_qutdn = !s2o_qutnt[26];

   wire [9:0] s3t_exp10 = s2o_exp10 - {9'd0,s3t_qutdn};

   wire [9:0] s3t_shr;
   wire [9:0] s3t_shl;

   assign s3t_shr = (s3t_exp10[9] | !(|s3t_exp10)) ?
       (10'd1 - s3t_exp10) - {9'd0,s3t_qutdn} : 0;

   assign s3t_shl = (s3t_exp10[9] | !(|s3t_exp10)) ?
       0 :
       s3t_exp10[8] ?
       0 : {9'd0,s3t_qutdn};


  // stage #3 outputs
  //   input related
  reg s3o_infa, s3o_infb,
      s3o_snan_a, s3o_qnan_a, s3o_snan_b, s3o_qnan_b;
  reg s3o_opa_0, s3o_opb_0;
  //   computation related
  reg s3o_sign;
  reg [8:0] s3o_exp9;
  reg [FRAC_WIDTH+3:0] s3o_qutnt;
  reg [5:0] s3o_shr;
  reg [5:0] s3o_shl;
  reg s3o_lost;

  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s3o_infa  <= s2o_infa;
      s3o_infb  <= s2o_infb;
      s3o_snan_a <= s2o_snan_a;
      s3o_qnan_a <= s2o_qnan_a;
      s3o_snan_b <= s2o_snan_b;
      s3o_qnan_b <= s2o_qnan_b;
      s3o_opa_0 <= s2o_opa_0;
      s3o_opb_0 <= s2o_opb_0;
        // computation related
      s3o_sign <= s2o_sign;
      
      if (s3t_exp10[9] | !(|s3t_exp10))
        s3o_exp9 <= 9'd1;
      else
        s3o_exp9 <= s3t_exp10[8:0];

      s3o_qutnt <= s2o_qutnt;

      s3o_shr <= (s3t_shr > 10'd26) ? 6'd27 : s3t_shr[5:0];
      s3o_shl <= s3t_shl[5:0];

      s3o_lost <= s2o_lost;
    end // (reset or flush) / advance
  end // always @ (posedge clk)

  // ready is special case
  reg s3o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      s3o_ready <= 0;
    else if(adv_i)
      s3o_ready <= s2o_ready;
  end // posedge clock


  /* Stage #4 */
  // Shifting the fraction and rounding
  reg [5:0] s4t_r_zeros;
    always @(s3o_qutnt)
      casez(s3o_qutnt) // synopsys full_case parallel_case
        27'b??????????????????????????1: s4t_r_zeros = 0;
        27'b?????????????????????????10: s4t_r_zeros = 1;
        27'b????????????????????????100: s4t_r_zeros = 2;
        27'b???????????????????????1000: s4t_r_zeros = 3;
        27'b??????????????????????10000: s4t_r_zeros = 4;
        27'b?????????????????????100000: s4t_r_zeros = 5;
        27'b????????????????????1000000: s4t_r_zeros = 6;
        27'b???????????????????10000000: s4t_r_zeros = 7;
        27'b??????????????????100000000: s4t_r_zeros = 8;
        27'b?????????????????1000000000: s4t_r_zeros = 9;
        27'b????????????????10000000000: s4t_r_zeros = 10;
        27'b???????????????100000000000: s4t_r_zeros = 11;
        27'b??????????????1000000000000: s4t_r_zeros = 12;
        27'b?????????????10000000000000: s4t_r_zeros = 13;
        27'b????????????100000000000000: s4t_r_zeros = 14;
        27'b???????????1000000000000000: s4t_r_zeros = 15;
        27'b??????????10000000000000000: s4t_r_zeros = 16;
        27'b?????????100000000000000000: s4t_r_zeros = 17;
        27'b????????1000000000000000000: s4t_r_zeros = 18;
        27'b???????10000000000000000000: s4t_r_zeros = 19;
        27'b??????100000000000000000000: s4t_r_zeros = 20;
        27'b?????1000000000000000000000: s4t_r_zeros = 21;
        27'b????10000000000000000000000: s4t_r_zeros = 22;
        27'b???100000000000000000000000: s4t_r_zeros = 23;
        27'b??1000000000000000000000000: s4t_r_zeros = 24;
        27'b?10000000000000000000000000: s4t_r_zeros = 25;
        27'b100000000000000000000000000: s4t_r_zeros = 26;
        27'b000000000000000000000000000: s4t_r_zeros = 27;
      endcase // casex (s3o_qutnt)

  reg [26:0] s4t_fract27;
  always @(s3o_qutnt or s3o_shr or s3o_shl) begin
    if (|s3o_shr)
      s4t_fract27 <= s3o_qutnt >> s3o_shr;
    else
      s4t_fract27 <= s3o_qutnt << s3o_shl;
  end // always

  // stage #4 outputs
  //   input related
  reg s4o_infa, s4o_infb,
      s4o_snan_a, s4o_qnan_a, s4o_snan_b, s4o_qnan_b;
  reg s4o_opa_0, s4o_opb_0;
  //   computation related
  reg s4o_sign;
  reg [8:0] s4o_exp9;
  reg [26:0] s4o_fract27;
  reg [5:0] s4o_shr;
  reg [5:0] s4o_r_zeros;
  reg s4o_lost;

  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s4o_infa  <= s3o_infa;
      s4o_infb  <= s3o_infb;
      s4o_snan_a <= s3o_snan_a;
      s4o_qnan_a <= s3o_qnan_a;
      s4o_snan_b <= s3o_snan_b;
      s4o_qnan_b <= s3o_qnan_b;
      s4o_opa_0 <= s3o_opa_0;
      s4o_opb_0 <= s3o_opb_0;
        // computation related
      s4o_sign <= s3o_sign;
      s4o_exp9 <= s4t_fract27[26] ? s3o_exp9 : s3o_exp9 - 9'd1;
      s4o_fract27 <= s4t_fract27;
      s4o_r_zeros <= s4t_r_zeros;
      s4o_shr <= s3o_shr;
      s4o_lost <= s3o_lost; // !!! lost just in reminder !!!
    end // (reset or flush) / advance
  end // posedge clock

  // ready is special case
  reg s4o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      s4o_ready <= 0;
    else if(adv_i)
      s4o_ready <= s3o_ready;
  end // posedge clock


  /* Stage #5 */
  // Rounding

  wire s5t_guard  = s4o_fract27[2];
  wire s5t_round  = s4o_fract27[1];
  wire s5t_sticky = s4o_fract27[0] | s4o_lost;

  wire s5t_roundup = rmode_i==2'b00 ? // round to nearest even
          s5t_guard & ((s5t_round | s5t_sticky) | s4o_fract27[3]) :
          rmode_i==2'b10 ? // round up
          (s5t_guard | s5t_round | s5t_sticky) & !s4o_sign :
          rmode_i==2'b11 ? // round down
          (s5t_guard | s5t_round | s5t_sticky) & s4o_sign :
          0; // round to zero(truncate = no rounding)

  wire [24:0] s5t_fract25_rnd;
  assign s5t_fract25_rnd = s5t_roundup ?
    {1'b0,s4o_fract27[26:3]} + 1 : {1'b0,s4o_fract27[26:3]};
    
  wire s5t_shr = s5t_fract25_rnd[24];

  // stage #5 outputs
  //   input related
  reg s5o_infa, s5o_infb,
      s5o_snan_a, s5o_qnan_a, s5o_snan_b, s5o_qnan_b;
  reg s5o_opa_0, s5o_opb_0;
  //   computation related
  reg s5o_sign;
  reg [8:0] s5o_exp9;
  reg [22:0] s5o_fract23;
  reg s5o_lost;

  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s5o_infa  <= s4o_infa;
      s5o_infb  <= s4o_infb;
      s5o_snan_a <= s4o_snan_a;
      s5o_qnan_a <= s4o_qnan_a;
      s5o_snan_b <= s4o_snan_b;
      s5o_qnan_b <= s4o_qnan_b;
      s5o_opa_0 <= s4o_opa_0;
      s5o_opb_0 <= s4o_opb_0;
        // computation related
      s5o_sign <= s4o_sign;
      s5o_exp9 <= s5t_shr ? s4o_exp9 + 9'd1 : s4o_exp9;
      s5o_fract23 <= s5t_shr ? s5t_fract25_rnd[23:1] : s5t_fract25_rnd[22:0];
      s5o_lost <= s4o_lost | (|s4o_fract27[2:0]) |
                  ((s4o_shr+{5'd0,s5t_shr}) > s4o_r_zeros);
    end // (reset or flush) / advance
  end // posedge clock

  // ready is special case
  reg s5o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      s5o_ready <= 0;
    else if(adv_i)
      s5o_ready <= s4o_ready;
  end // posedge clock

  /* Stage #6 : form output */
  // input nans
  wire s6t_anan_a  = s5o_snan_a | s5o_qnan_a;
  wire s6t_anan_b  = s5o_snan_b | s5o_qnan_b;
  wire s6t_snan_in = s5o_snan_a | s5o_snan_b;
  wire s6t_anan_in = s6t_anan_a | s6t_anan_b;  

  // "infs" (actually exp==8'hff)
  //wire s6t_expa_ff = s6t_anan_a | s5o_infa;
  //wire s6t_expb_ff = s6t_anan_b | s5o_infb;

  //  0/0, inf/inf -> invalid flag, qnan result
  wire s6t_inv    = (s5o_opa_0 & s5o_opb_0) | 
                    (s5o_infa & s5o_infb) | 
                    s6t_snan_in;
  wire s6t_opc_nan = s6t_anan_in | s6t_inv;

  wire s6t_inf_result = (&s5o_exp9[7:0]) | s5o_exp9[8] | s5o_opb_0;

  wire s6t_ovf = s6t_inf_result & (!s5o_infa) & (!s5o_opb_0);

  wire s6t_ine = !s5o_opa_0 & !s5o_opb_0 & !s5o_infa & !s5o_infb &
                 (s5o_lost | s6t_ovf);

  wire [31:0] s6t_opc =
    s6t_opc_nan ? {s5o_sign,QNAN} :
    (s5o_infa | s6t_ovf | s6t_inf_result) ? {s5o_sign,INF} :
    (s5o_opa_0 | s5o_infb) ? {s5o_sign,31'd0} :
    {s5o_sign,s5o_exp9[7:0],s5o_fract23};

    // Output register
  always @(posedge clk) begin
    if(adv_i) begin
      opc_o   <= s6t_opc;
      ine_o   <= s6t_ine;
      inv_o   <= s6t_inv;
      ovf_o   <= (&s6t_opc[30:23]) & s6t_ine;
      inf_o   <= (&s6t_opc[30:23]) & !s6t_opc_nan;
      unf_o   <= (!(|s6t_opc[30:0])) & s6t_ine;
      zer_o   <= !(|s6t_opc[30:0]);
      dbz_o   <= s5o_opb_0 & !s5o_opa_0 & !s6t_inv & !s5o_infa;
    end
  end // posedge clock

  // ready is special case
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      ready_o <= 0;
    else if(adv_i)
      ready_o <= s5o_ready;
  end // posedge clock

endmodule // pfpu32_div
