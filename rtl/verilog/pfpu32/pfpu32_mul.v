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
   input      [31:0] opa_i,
   input      [31:0] opb_i,
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
  localparam EXP_WIDTH = 8;
  localparam FRAC_WIDTH = 23;

  /*
     Any stage's output is registered.
     Definitions:
       s??o_name - "S"tage number "??", "O"utput
       s??t_name - "S"tage number "??", "T"emporary (internally)
  */


  /* Stage #1: pre-multiplier normalization */

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
  wire s1t_op_0 = !((|opa_i[30:0]) & (|opb_i[30:0]));

    // restore hidden "1"
      // insert leading zeros to signal unsigned values
      // for potential usage DSP blocks of a FPGA
  wire [12:0] s1t_fract13_al = {1'b0, s1t_fracta[11:0]};
  wire [12:0] s1t_fract13_ah = {1'b0, !s1t_opa_dn, s1t_fracta[22:12]};
  wire [12:0] s1t_fract13_bl = {1'b0, s1t_fractb[11:0]};
  wire [12:0] s1t_fract13_bh = {1'b0, !s1t_opb_dn, s1t_fractb[22:12]};

  wire [EXP_WIDTH+1:0] s1t_expa_10 = {2'd0, s1t_expa} + {9'd0, s1t_opa_dn};
  wire [EXP_WIDTH+1:0] s1t_expb_10 = {2'd0, s1t_expb} + {9'd0, s1t_opb_dn};

  wire [EXP_WIDTH+1:0] s1t_exp10 = s1t_expa_10 + s1t_expb_10 - 10'b0001111111;
   
  // stage #1 outputs
  //   input related
  reg s1o_infa, s1o_infb,
      s1o_snan_a, s1o_qnan_a, s1o_snan_b, s1o_qnan_b;
  reg s1o_op_0;
  //   computation related
  reg s1o_sign;
  reg [EXP_WIDTH+1:0] s1o_exp10;
  reg [25:0] s1o_fract26_albl;
  reg [25:0] s1o_fract26_albh;
  reg [25:0] s1o_fract26_ahbl;
  reg [25:0] s1o_fract26_ahbh;
 
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
      s1o_op_0  <= s1t_op_0;
        // computation related
      s1o_sign <= s1t_signa ^ s1t_signb;
      s1o_exp10 <= s1t_exp10;
      s1o_fract26_albl <= s1t_fract13_al * s1t_fract13_bl;
      s1o_fract26_albh <= s1t_fract13_al * s1t_fract13_bh;
      s1o_fract26_ahbl <= s1t_fract13_ah * s1t_fract13_bl;
      s1o_fract26_ahbh <= s1t_fract13_ah * s1t_fract13_bh;
    end // (reset or flush) / advance
  end // posedge clock

  // ready is special case
  reg s1o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      s1o_ready <= 0;
    else if(adv_i)
      s1o_ready <= start_i;
  end // posedge clock


  /* Stage #2: multiplier */
  
  wire  [47:0] s2t_fract48;
  assign s2t_fract48 = {s1o_fract26_ahbh[23:0],  24'd0} + 
                       {10'd0, s1o_fract26_ahbl, 12'd0} + 
                       {10'd0, s1o_fract26_albh, 12'd0} + 
                       {24'd0,  s1o_fract26_albl[23:0]};

  // stage #2 outputs
  //   input related
  reg s2o_infa, s2o_infb,
      s2o_snan_a, s2o_qnan_a, s2o_snan_b, s2o_qnan_b;
  reg s2o_op_0;
  //   computation related
  reg s2o_sign;
  reg [EXP_WIDTH+1:0] s2o_exp10;
  reg [47:0] s2o_fract48;

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
      s2o_op_0  <= s1o_op_0;
        // computation related
      s2o_sign <= s1o_sign;
      s2o_exp10 <= s1o_exp10;
      s2o_fract48 <= s2t_fract48;
    end // (reset or flush) / advance
  end // posedge clock

  // ready is special case
  reg s2o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i)
      s2o_ready <= 0;
    else if(adv_i)
      s2o_ready <= s1o_ready;
  end // posedge clock


  /*
    Stages #3, #4, #5 and #6 : post multiplier normalization
  */


  /* Stage #3 */
  // figure out the exponent and howmuch the fraction has to be shiftd
  // right/left

  reg [5:0] s3t_zeros;
  always @(s2o_fract48[46:1]) begin
    casez(s2o_fract48[46:1])  // synopsys full_case parallel_case
      46'b1?????????????????????????????????????????????: s3t_zeros =  0;
      46'b01????????????????????????????????????????????: s3t_zeros =  1;
      46'b001???????????????????????????????????????????: s3t_zeros =  2;
      46'b0001??????????????????????????????????????????: s3t_zeros =  3;
      46'b00001?????????????????????????????????????????: s3t_zeros =  4;
      46'b000001????????????????????????????????????????: s3t_zeros =  5;
      46'b0000001???????????????????????????????????????: s3t_zeros =  6;
      46'b00000001??????????????????????????????????????: s3t_zeros =  7;
      46'b000000001?????????????????????????????????????: s3t_zeros =  8;
      46'b0000000001????????????????????????????????????: s3t_zeros =  9;
      46'b00000000001???????????????????????????????????: s3t_zeros =  10;
      46'b000000000001??????????????????????????????????: s3t_zeros =  11;
      46'b0000000000001?????????????????????????????????: s3t_zeros =  12;
      46'b00000000000001????????????????????????????????: s3t_zeros =  13;
      46'b000000000000001???????????????????????????????: s3t_zeros =  14;
      46'b0000000000000001??????????????????????????????: s3t_zeros =  15;
      46'b00000000000000001?????????????????????????????: s3t_zeros =  16;
      46'b000000000000000001????????????????????????????: s3t_zeros =  17;
      46'b0000000000000000001???????????????????????????: s3t_zeros =  18;
      46'b00000000000000000001??????????????????????????: s3t_zeros =  19;
      46'b000000000000000000001?????????????????????????: s3t_zeros =  20;
      46'b0000000000000000000001????????????????????????: s3t_zeros =  21;
      46'b00000000000000000000001???????????????????????: s3t_zeros =  22;
      46'b000000000000000000000001??????????????????????: s3t_zeros =  23;
      46'b0000000000000000000000001?????????????????????: s3t_zeros =  24;
      46'b00000000000000000000000001????????????????????: s3t_zeros =  25;
      46'b000000000000000000000000001???????????????????: s3t_zeros =  26;
      46'b0000000000000000000000000001??????????????????: s3t_zeros =  27;
      46'b00000000000000000000000000001?????????????????: s3t_zeros =  28;
      46'b000000000000000000000000000001????????????????: s3t_zeros =  29;
      46'b0000000000000000000000000000001???????????????: s3t_zeros =  30;
      46'b00000000000000000000000000000001??????????????: s3t_zeros =  31;
      46'b000000000000000000000000000000001?????????????: s3t_zeros =  32;
      46'b0000000000000000000000000000000001????????????: s3t_zeros =  33;
      46'b00000000000000000000000000000000001???????????: s3t_zeros =  34;
      46'b000000000000000000000000000000000001??????????: s3t_zeros =  35;
      46'b0000000000000000000000000000000000001?????????: s3t_zeros =  36;
      46'b00000000000000000000000000000000000001????????: s3t_zeros =  37;
      46'b000000000000000000000000000000000000001???????: s3t_zeros =  38;
      46'b0000000000000000000000000000000000000001??????: s3t_zeros =  39;
      46'b00000000000000000000000000000000000000001?????: s3t_zeros =  40;
      46'b000000000000000000000000000000000000000001????: s3t_zeros =  41;
      46'b0000000000000000000000000000000000000000001???: s3t_zeros =  42;
      46'b00000000000000000000000000000000000000000001??: s3t_zeros =  43;
      46'b000000000000000000000000000000000000000000001?: s3t_zeros =  44;
      46'b0000000000000000000000000000000000000000000001: s3t_zeros =  45;
      46'b0000000000000000000000000000000000000000000000: s3t_zeros =  46;
    endcase // casex (s2o_fract48[46:1])
  end // always

  wire s3t_carry = s2o_fract48[47];
  wire [5:0] s3t_l_zeros = s3t_zeros & {6{!s3t_carry}};

  wire [9:0] s3t_exp10a = s2o_exp10 + {9'd0,s3t_carry};
  wire [9:0] s3t_exp10b = s3t_exp10a - {4'd0,s3t_l_zeros};

  wire [9:0] s3t_shr;
  assign s3t_shr = (s3t_exp10a[9] | !(|s3t_exp10a)) ?
        10'd1 - s3t_exp10a + {9'd0,s3t_carry} :
        (s3t_exp10b[9] | !(|s3t_exp10b)) ?
        0 :
        s3t_exp10b[8] ?
        0 : {9'd0,s3t_carry};

  wire [9:0] s3t_shl;
  assign s3t_shl =
        // (e10a =< 0): borrowing from exp isn't possible
      (s3t_exp10a[9] | !(|s3t_exp10a)) ? 0 :
        // borrowing from e10a is possible (e10a > 0)
        // and number of fract's nlz >= borrowing volume (e10b =< 0)
        // but we can't borrow more than (e10a - 1)
        // so denormalized result is possible
      (s3t_exp10b[9] | !(|s3t_exp10b)) ? (s3t_exp10a - 10'd1) :
        // (Bacherov: ??? overflow ???)
      s3t_exp10b[8] ? 0 :
        // (Bacherov: ??? no overflow & nlz<e10a ???)
      {4'd0,s3t_l_zeros};

  // stage #3 outputs
  //   input related
  reg s3o_infa, s3o_infb,
      s3o_snan_a, s3o_qnan_a, s3o_snan_b, s3o_qnan_b;
  reg s3o_op_0;
  //   computation related
  reg s3o_sign;
  reg [8:0] s3o_exp9;
  reg [47:0] s3o_fract48;
  reg [5:0] s3o_shr;
  reg [5:0] s3o_shl;

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
      s3o_op_0  <= s2o_op_0;
        // computation related
      s3o_sign <= s2o_sign;
      
      if ((s3t_exp10a[9] | !(|s3t_exp10a)))
        s3o_exp9 <= 9'd1;
      else if (s3t_exp10b[9] | !(|s3t_exp10b))
        s3o_exp9 <= 9'd1;
      else if (s3t_exp10b[8])
        s3o_exp9 <= 9'b011111111;
      else
        s3o_exp9 <= s3t_exp10b[8:0];

      if (s3t_shr[6])
        s3o_shr <= {6{1'b1}};
      else
        s3o_shr <= s3t_shr[5:0];

      s3o_shl <= s3t_shl[5:0];
      
      s3o_fract48 <= s2o_fract48;
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
  always @(s3o_fract48) begin
    casez(s3o_fract48) // synopsys full_case parallel_case
      48'b???????????????????????????????????????????????1: s4t_r_zeros =  0;
      48'b??????????????????????????????????????????????10: s4t_r_zeros =  1;
      48'b?????????????????????????????????????????????100: s4t_r_zeros =  2;
      48'b????????????????????????????????????????????1000: s4t_r_zeros =  3;
      48'b???????????????????????????????????????????10000: s4t_r_zeros =  4;
      48'b??????????????????????????????????????????100000: s4t_r_zeros =  5;
      48'b?????????????????????????????????????????1000000: s4t_r_zeros =  6;
      48'b????????????????????????????????????????10000000: s4t_r_zeros =  7;
      48'b???????????????????????????????????????100000000: s4t_r_zeros =  8;
      48'b??????????????????????????????????????1000000000: s4t_r_zeros =  9;
      48'b?????????????????????????????????????10000000000: s4t_r_zeros =  10;
      48'b????????????????????????????????????100000000000: s4t_r_zeros =  11;
      48'b???????????????????????????????????1000000000000: s4t_r_zeros =  12;
      48'b??????????????????????????????????10000000000000: s4t_r_zeros =  13;
      48'b?????????????????????????????????100000000000000: s4t_r_zeros =  14;
      48'b????????????????????????????????1000000000000000: s4t_r_zeros =  15;
      48'b???????????????????????????????10000000000000000: s4t_r_zeros =  16;
      48'b??????????????????????????????100000000000000000: s4t_r_zeros =  17;
      48'b?????????????????????????????1000000000000000000: s4t_r_zeros =  18;
      48'b????????????????????????????10000000000000000000: s4t_r_zeros =  19;
      48'b???????????????????????????100000000000000000000: s4t_r_zeros =  20;
      48'b??????????????????????????1000000000000000000000: s4t_r_zeros =  21;
      48'b?????????????????????????10000000000000000000000: s4t_r_zeros =  22;
      48'b????????????????????????100000000000000000000000: s4t_r_zeros =  23;
      48'b???????????????????????1000000000000000000000000: s4t_r_zeros =  24;
      48'b??????????????????????10000000000000000000000000: s4t_r_zeros =  25;
      48'b?????????????????????100000000000000000000000000: s4t_r_zeros =  26;
      48'b????????????????????1000000000000000000000000000: s4t_r_zeros =  27;
      48'b???????????????????10000000000000000000000000000: s4t_r_zeros =  28;
      48'b??????????????????100000000000000000000000000000: s4t_r_zeros =  29;
      48'b?????????????????1000000000000000000000000000000: s4t_r_zeros =  30;
      48'b????????????????10000000000000000000000000000000: s4t_r_zeros =  31;
      48'b???????????????100000000000000000000000000000000: s4t_r_zeros =  32;
      48'b??????????????1000000000000000000000000000000000: s4t_r_zeros =  33;
      48'b?????????????10000000000000000000000000000000000: s4t_r_zeros =  34;
      48'b????????????100000000000000000000000000000000000: s4t_r_zeros =  35;
      48'b???????????1000000000000000000000000000000000000: s4t_r_zeros =  36;
      48'b??????????10000000000000000000000000000000000000: s4t_r_zeros =  37;
      48'b?????????100000000000000000000000000000000000000: s4t_r_zeros =  38;
      48'b????????1000000000000000000000000000000000000000: s4t_r_zeros =  39;
      48'b???????10000000000000000000000000000000000000000: s4t_r_zeros =  40;
      48'b??????100000000000000000000000000000000000000000: s4t_r_zeros =  41;
      48'b?????1000000000000000000000000000000000000000000: s4t_r_zeros =  42;
      48'b????10000000000000000000000000000000000000000000: s4t_r_zeros =  43;
      48'b???100000000000000000000000000000000000000000000: s4t_r_zeros =  44;
      48'b??1000000000000000000000000000000000000000000000: s4t_r_zeros =  45;
      48'b?10000000000000000000000000000000000000000000000: s4t_r_zeros =  46;
      48'b100000000000000000000000000000000000000000000000: s4t_r_zeros =  47;
      48'b000000000000000000000000000000000000000000000000: s4t_r_zeros =  48;
    endcase // casex (s3o_fract48)
  end // always

  // shifter
  reg [47:0] s4t_fract48;
  always @(s3o_fract48 or s3o_shr or s3o_shl) begin
    if (|s3o_shr)
      s4t_fract48 = s3o_fract48 >> s3o_shr;
    else
      s4t_fract48 = s3o_fract48 << s3o_shl;  
  end // always
 
  // stage #4 outputs
  //   input related
  reg s4o_infa, s4o_infb,
      s4o_snan_a, s4o_qnan_a, s4o_snan_b, s4o_qnan_b;
  reg s4o_op_0;
  //   computation related
  reg s4o_sign;
  reg [8:0] s4o_exp9;
  reg [47:0] s4o_fract48;
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
      s4o_op_0  <= s3o_op_0;
        // computation related
      s4o_sign <= s3o_sign;
      s4o_exp9 <= s4t_fract48[46] ? s3o_exp9 : s3o_exp9 - 9'd1;
      s4o_fract48 <= s4t_fract48;

      if (|s3o_shr)
        s4o_lost <= (s3o_shr > s4t_r_zeros); // due to right shift
      else
        s4o_lost <= 0;
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


  /* Stage #5:  Rounding */

  //                  23
  //                 |
  // xx00000000000000000000000grsxxxxxxxxxxxxxxxxxxxx
  // guard bit: s4o_fract48[23] (LSB of output)
  // round bit: s4o_fract48[22]
  wire s5t_guard = s4o_fract48[22];
  wire s5t_round = s4o_fract48[21];
  //assign s5t_sticky = (|s4o_fract48[20:0]) | s6t_lost;
  wire s5t_sticky = (|s4o_fract48[20:0]) | s4o_lost; // take into account the part lost due to right shift

  wire s5t_roundup = rmode_i==2'b00 ? // round to nearest even
        s5t_guard & ((s5t_round | s5t_sticky) | s4o_fract48[23]) :
        rmode_i==2'b10 ? // round up
        (s5t_guard | s5t_round | s5t_sticky) & !s4o_sign :
        rmode_i==2'b11 ? // round down
        (s5t_guard | s5t_round | s5t_sticky) & s4o_sign :
        0; // round to zero(truncate = no rounding)

  // stage #5 outputs
  //   input related
  reg s5o_infa, s5o_infb,
      s5o_snan_a, s5o_qnan_a, s5o_snan_b, s5o_qnan_b;
  reg s5o_op_0;
  //   computation related
  reg s5o_sign;
  reg [8:0] s5o_exp9;
  reg [24:0] s5o_fract25;
  reg s5o_dn2n; // denormalized to normalized
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
      s5o_op_0  <= s4o_op_0;
        // computation related
      s5o_sign <= s4o_sign;
      s5o_exp9 <= s4o_exp9;
      s5o_lost <= s4o_lost | (|s4o_fract48[22:0]);
      
      if (s5t_roundup) begin
        s5o_fract25 <= s4o_fract48[47:23] + 1;
        s5o_dn2n <= (!s4o_fract48[46]) & (&s4o_fract48[45:23]);
      end
      else begin
        s5o_fract25 <= s4o_fract48[47:23];
        s5o_dn2n <= 0;
      end
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


  /* Stage #6: finish rounding and form output */ 
  // input nans
  wire s6t_anan_a  = s5o_snan_a | s5o_qnan_a;
  wire s6t_anan_b  = s5o_snan_b | s5o_qnan_b;
  wire s6t_snan_in = s5o_snan_a | s5o_snan_b;
  wire s6t_anan_in = s6t_anan_a | s6t_anan_b;

  // "infs" (actually exp==8'hff)
  wire s6t_expa_ff = s6t_anan_a | s5o_infa;
  wire s6t_expb_ff = s6t_anan_b | s5o_infb;

  //  0 * inf -> invalid flag, qnan output
  wire s6t_inv = ((s6t_expa_ff | s6t_expb_ff) & s5o_op_0) |
                 s6t_snan_in;

  wire s6t_opc_nan = s6t_anan_in | s6t_inv;

  wire s6t_shr  = s5o_fract25[24];
  wire s6t_lost = s5o_lost | (s6t_shr & s5o_fract25[0]);  // or one more lost due to one more one shift

  wire [8:0] s6t_exp9;
  assign s6t_exp9 =
    ((s6t_shr | s5o_dn2n) & (s5o_exp9!=9'b011111111)) ? (s5o_exp9 + 1) :
    s5o_exp9;

  wire [22:0] s6t_fract23;
  assign s6t_fract23 =
    (s6t_shr & (s5o_exp9!=9'b011111111)) ? s5o_fract25[23:1] :
    s5o_fract25[22:0];


  wire s6t_ovf = (s6t_exp9==9'b011111111) & !(s6t_expa_ff | s6t_expb_ff);

  wire s6t_ine = (!s5o_op_0) & (s6t_lost | s6t_ovf);

  wire [31:0] s6t_opc;
  assign s6t_opc =
    s6t_opc_nan ? {s5o_sign,QNAN} :
    (s6t_expa_ff | s6t_expb_ff | s6t_ovf) ? {s5o_sign,INF} :
    (s4t_r_zeros==48) ? {s5o_sign,31'd0} :
    {s5o_sign,s6t_exp9[7:0],s6t_fract23};

    // Output register
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst | flush_i) begin
      opc_o   <= 0;
      ine_o   <= 0;
      inv_o   <= 0;
      ovf_o   <= 0;
      inf_o   <= 0;
      unf_o   <= 0;
      zer_o   <= 0;
    end
    else if(adv_i) begin
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

endmodule // pfpu32_mul
