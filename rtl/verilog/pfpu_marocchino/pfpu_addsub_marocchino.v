//////////////////////////////////////////////////////////////////////
//                                                                  //
//    pfpu_addsub_marocchino                                        //
//                                                                  //
//    This file is part of the mor1kx project                       //
//    https://github.com/openrisc/mor1kx                            //
//                                                                  //
//    Description                                                   //
//    addition/subtraction pipeline for single and double precision //
//    floating point numbers for MAROCCHINO pipeline                //
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


module pfpu_addsub_marocchino
(
  // clocks and resets
  input             clk,
  input             rst,
  // ADD/SUB pipe controls
  input             pipeline_flush_i,
  input             add_start_i,
  input             exec_op_fpxx_sub_i,         // 1: substruction, 0: addition
  output            add_taking_op_o,
  output reg        add_rdy_o,        // ready
  input             rnd_taking_add_i,
  // input 'a' related values
  input             signa_i,
  input      [12:0] exp13a_i,
  input      [52:0] fract53a_i,
  // input 'b' related values
  input             signb_i,
  input      [12:0] exp13b_i,
  input      [52:0] fract53b_i,
  // 'a'/'b' related
  input             exec_op_fp64_arith_i,
  input             opc_0_i,         // force intrmadiate result to 0
  input             addsub_agtb_i,
  input             addsub_aeqb_i,
  // outputs
  output reg        add_sign_o,      // signum
  output reg        add_sub_0_o,     // flag that actual substruction is performed and result is zero
  output reg  [5:0] add_shl_o,       // do left shift in align stage
  output reg [12:0] add_exp13shl_o,  // exponent for left shift align
  output reg [12:0] add_exp13sh0_o,  // exponent for no shift in align
  output reg [56:0] add_fract57_o    // fractional with appended {r,s} bits
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
  wire s1_adv  = add_start_i & ~s1_busy;
  wire s2_adv  = s1o_ready   & ~s2_busy;
  wire s3_adv  = s2o_ready   & ~s3_busy;

  // ADD/SUB pipe takes operands for computation
  assign add_taking_op_o = s1_adv;


  /* Stage #1: pre addition / substraction align */


    // signums for calculation
  wire s1t_calc_signa = signa_i;
  wire s1t_calc_signb = (signb_i ^ exec_op_fpxx_sub_i);

    // not shifted operand and its signum
  wire [52:0] s1t_fract53_nsh =
    addsub_agtb_i ? fract53a_i : fract53b_i;

    // operand for right shift
  wire [52:0] s1t_fract53_fsh =
    addsub_agtb_i ? fract53b_i : fract53a_i;

    // shift amount
  wire [12:0] s1t_exp_diff =
    addsub_agtb_i ? (exp13a_i - exp13b_i) :
                    (exp13b_i - exp13a_i);

  // limiter by 63
  wire [5:0] s1t_shr = s1t_exp_diff[5:0] | {6{|s1t_exp_diff[12:6]}};

  // stage #1 outputs
  reg        s1o_aeqb;
  reg  [5:0] s1o_shr;
  reg        s1o_sign_nsh;
  reg        s1o_op_sub;
  reg [12:0] s1o_exp13c;
  reg [52:0] s1o_fract53_nsh;
  reg [52:0] s1o_fract53_fsh;
  reg        s1o_op_fp64_arith;
  //  registering
  always @(posedge clk) begin
    if (s1_adv) begin
      s1o_aeqb          <= addsub_aeqb_i;
      s1o_shr           <= s1t_shr & {6{~opc_0_i}};
      s1o_sign_nsh      <= addsub_agtb_i ? s1t_calc_signa : s1t_calc_signb;
      s1o_op_sub        <= s1t_calc_signa ^ s1t_calc_signb;
      s1o_exp13c        <= addsub_agtb_i ? exp13a_i : exp13b_i;
      s1o_fract53_nsh   <= s1t_fract53_nsh & {53{~opc_0_i}};
      s1o_fract53_fsh   <= s1t_fract53_fsh & {53{~opc_0_i}};
      s1o_op_fp64_arith <= exec_op_fp64_arith_i;
    end // advance
  end // @clock

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
  end // @clock


  /* Stage 2: multiplex and shift */


  // shifter
  wire [54:0] s2t_fract55_fsh = {s1o_fract53_fsh,2'd0};
  wire [54:0] s2t_fract55_shr = s2t_fract55_fsh >> s1o_shr;

  // sticky
  reg s2t_sticky;
  always @(s1o_shr or s1o_fract53_fsh) begin
    // synthesis parallel_case full_case
    case (s1o_shr)
      6'd0, 6'd1, 6'd2 : s2t_sticky = 1'b0; // two added zero bits
      6'd3 : s2t_sticky = s1o_fract53_fsh[0];
      6'd4 : s2t_sticky = |s1o_fract53_fsh[1:0];
      6'd5 : s2t_sticky = |s1o_fract53_fsh[2:0];
      6'd6 : s2t_sticky = |s1o_fract53_fsh[3:0];
      6'd7 : s2t_sticky = |s1o_fract53_fsh[4:0];
      6'd8 : s2t_sticky = |s1o_fract53_fsh[5:0];
      6'd9 : s2t_sticky = |s1o_fract53_fsh[6:0];
      6'd10: s2t_sticky = |s1o_fract53_fsh[7:0];
      6'd11: s2t_sticky = |s1o_fract53_fsh[8:0];
      6'd12: s2t_sticky = |s1o_fract53_fsh[9:0];
      6'd13: s2t_sticky = |s1o_fract53_fsh[10:0];
      6'd14: s2t_sticky = |s1o_fract53_fsh[11:0];
      6'd15: s2t_sticky = |s1o_fract53_fsh[12:0];
      6'd16: s2t_sticky = |s1o_fract53_fsh[13:0];
      6'd17: s2t_sticky = |s1o_fract53_fsh[14:0];
      6'd18: s2t_sticky = |s1o_fract53_fsh[15:0];
      6'd19: s2t_sticky = |s1o_fract53_fsh[16:0];
      6'd20: s2t_sticky = |s1o_fract53_fsh[17:0];
      6'd21: s2t_sticky = |s1o_fract53_fsh[18:0];
      6'd22: s2t_sticky = |s1o_fract53_fsh[19:0];
      6'd23: s2t_sticky = |s1o_fract53_fsh[20:0];
      6'd24: s2t_sticky = |s1o_fract53_fsh[21:0];
      6'd25: s2t_sticky = |s1o_fract53_fsh[22:0];
      6'd26: s2t_sticky = |s1o_fract53_fsh[23:0];
      6'd27: s2t_sticky = |s1o_fract53_fsh[24:0];
      6'd28: s2t_sticky = |s1o_fract53_fsh[25:0];
      6'd29: s2t_sticky = |s1o_fract53_fsh[26:0];
      6'd30: s2t_sticky = |s1o_fract53_fsh[27:0];
      6'd31: s2t_sticky = |s1o_fract53_fsh[28:0];
      6'd32: s2t_sticky = |s1o_fract53_fsh[29:0];
      6'd33: s2t_sticky = |s1o_fract53_fsh[30:0];
      6'd34: s2t_sticky = |s1o_fract53_fsh[31:0];
      6'd35: s2t_sticky = |s1o_fract53_fsh[32:0];
      6'd36: s2t_sticky = |s1o_fract53_fsh[33:0];
      6'd37: s2t_sticky = |s1o_fract53_fsh[34:0];
      6'd38: s2t_sticky = |s1o_fract53_fsh[35:0];
      6'd39: s2t_sticky = |s1o_fract53_fsh[36:0];
      6'd40: s2t_sticky = |s1o_fract53_fsh[37:0];
      6'd41: s2t_sticky = |s1o_fract53_fsh[38:0];
      6'd42: s2t_sticky = |s1o_fract53_fsh[39:0];
      6'd43: s2t_sticky = |s1o_fract53_fsh[40:0];
      6'd44: s2t_sticky = |s1o_fract53_fsh[41:0];
      6'd45: s2t_sticky = |s1o_fract53_fsh[42:0];
      6'd46: s2t_sticky = |s1o_fract53_fsh[43:0];
      6'd47: s2t_sticky = |s1o_fract53_fsh[44:0];
      6'd48: s2t_sticky = |s1o_fract53_fsh[45:0];
      6'd49: s2t_sticky = |s1o_fract53_fsh[46:0];
      6'd50: s2t_sticky = |s1o_fract53_fsh[47:0];
      6'd51: s2t_sticky = |s1o_fract53_fsh[48:0];
      6'd52: s2t_sticky = |s1o_fract53_fsh[49:0];
      6'd53: s2t_sticky = |s1o_fract53_fsh[50:0];
      6'd54: s2t_sticky = |s1o_fract53_fsh[51:0];
      default: s2t_sticky = |s1o_fract53_fsh;
    endcase
  end



  // stage #2 outputs
  reg        s2o_signc;
  reg [12:0] s2o_exp13c;
  reg [54:0] s2o_fract55_shr;
  reg [52:0] s2o_fract53_nsh;
  reg        s2o_op_sub;
  reg        s2o_sub_0;       // actual operation is substruction and the result is zero
  reg        s2o_sticky;      // rounding support
  reg        s2o_op_fp64_arith;
  //  registering
  always @(posedge clk) begin
    if (s2_adv) begin
      s2o_signc         <= s1o_sign_nsh;
      s2o_exp13c        <= s1o_exp13c;
      s2o_fract55_shr   <= s2t_fract55_shr;
      s2o_fract53_nsh   <= s1o_fract53_nsh;
      s2o_op_sub        <= s1o_op_sub;
      s2o_sub_0         <= s1o_aeqb & s1o_op_sub;
      s2o_sticky        <= s2t_sticky;
      s2o_op_fp64_arith <= s1o_op_fp64_arith;
    end // advance
  end // @clock

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
  end // @clock


  /* Stage 4: add/sum and update exponent */

  wire [56:0] s3t_fract57_shr = {1'b0,s2o_fract55_shr,s2o_sticky};

  wire [56:0] s3t_fract57_add = {1'b0,s2o_fract53_nsh,3'd0} +
                                (s3t_fract57_shr ^ {57{s2o_op_sub}}) +
                                {56'd0,s2o_op_sub};

  wire [55:0] s3t_fract56_add = s3t_fract57_add[56:1];

  // for possible left shift
  // [56] bit is right shift flag
  reg [5:0] s3t_nlz;
  always @(s3t_fract56_add) begin
    // synthesis parallel_case full_case
    casez (s3t_fract56_add)
      56'b1???????????????????????????????????????????????????????: s3t_nlz =  6'd0; // [56] bit: shift right
      56'b01??????????????????????????????????????????????????????: s3t_nlz =  6'd0; // 1 is in place
      56'b001?????????????????????????????????????????????????????: s3t_nlz =  6'd1;
      56'b0001????????????????????????????????????????????????????: s3t_nlz =  6'd2;
      56'b00001???????????????????????????????????????????????????: s3t_nlz =  6'd3;
      56'b000001??????????????????????????????????????????????????: s3t_nlz =  6'd4;
      56'b0000001?????????????????????????????????????????????????: s3t_nlz =  6'd5;
      56'b00000001????????????????????????????????????????????????: s3t_nlz =  6'd6;
      56'b000000001???????????????????????????????????????????????: s3t_nlz =  6'd7;
      56'b0000000001??????????????????????????????????????????????: s3t_nlz =  6'd8;
      56'b00000000001?????????????????????????????????????????????: s3t_nlz =  6'd9;
      56'b000000000001????????????????????????????????????????????: s3t_nlz = 6'd10;
      56'b0000000000001???????????????????????????????????????????: s3t_nlz = 6'd11;
      56'b00000000000001??????????????????????????????????????????: s3t_nlz = 6'd12;
      56'b000000000000001?????????????????????????????????????????: s3t_nlz = 6'd13;
      56'b0000000000000001????????????????????????????????????????: s3t_nlz = 6'd14;
      56'b00000000000000001???????????????????????????????????????: s3t_nlz = 6'd15;
      56'b000000000000000001??????????????????????????????????????: s3t_nlz = 6'd16;
      56'b0000000000000000001?????????????????????????????????????: s3t_nlz = 6'd17;
      56'b00000000000000000001????????????????????????????????????: s3t_nlz = 6'd18;
      56'b000000000000000000001???????????????????????????????????: s3t_nlz = 6'd19;
      56'b0000000000000000000001??????????????????????????????????: s3t_nlz = 6'd20;
      56'b00000000000000000000001?????????????????????????????????: s3t_nlz = 6'd21;
      56'b000000000000000000000001????????????????????????????????: s3t_nlz = 6'd22;
      56'b0000000000000000000000001???????????????????????????????: s3t_nlz = 6'd23;
      56'b00000000000000000000000001??????????????????????????????: s3t_nlz = 6'd24;
      56'b000000000000000000000000001?????????????????????????????: s3t_nlz = 6'd25;
      56'b0000000000000000000000000001????????????????????????????: s3t_nlz = 6'd26;
      56'b00000000000000000000000000001???????????????????????????: s3t_nlz = 6'd27;
      56'b000000000000000000000000000001??????????????????????????: s3t_nlz = 6'd28;
      56'b0000000000000000000000000000001?????????????????????????: s3t_nlz = 6'd29;
      56'b00000000000000000000000000000001????????????????????????: s3t_nlz = 6'd30;
      56'b000000000000000000000000000000001???????????????????????: s3t_nlz = 6'd31;
      56'b0000000000000000000000000000000001??????????????????????: s3t_nlz = 6'd32;
      56'b00000000000000000000000000000000001?????????????????????: s3t_nlz = 6'd33;
      56'b000000000000000000000000000000000001????????????????????: s3t_nlz = 6'd34;
      56'b0000000000000000000000000000000000001???????????????????: s3t_nlz = 6'd35;
      56'b00000000000000000000000000000000000001??????????????????: s3t_nlz = 6'd36;
      56'b000000000000000000000000000000000000001?????????????????: s3t_nlz = 6'd37;
      56'b0000000000000000000000000000000000000001????????????????: s3t_nlz = 6'd38;
      56'b00000000000000000000000000000000000000001???????????????: s3t_nlz = 6'd39;
      56'b000000000000000000000000000000000000000001??????????????: s3t_nlz = 6'd40;
      56'b0000000000000000000000000000000000000000001?????????????: s3t_nlz = 6'd41;
      56'b00000000000000000000000000000000000000000001????????????: s3t_nlz = 6'd42;
      56'b000000000000000000000000000000000000000000001???????????: s3t_nlz = 6'd43;
      56'b0000000000000000000000000000000000000000000001??????????: s3t_nlz = 6'd44;
      56'b00000000000000000000000000000000000000000000001?????????: s3t_nlz = 6'd45;
      56'b000000000000000000000000000000000000000000000001????????: s3t_nlz = 6'd46;
      56'b0000000000000000000000000000000000000000000000001???????: s3t_nlz = 6'd47;
      56'b00000000000000000000000000000000000000000000000001??????: s3t_nlz = 6'd48;
      56'b000000000000000000000000000000000000000000000000001?????: s3t_nlz = 6'd49;
      56'b0000000000000000000000000000000000000000000000000001????: s3t_nlz = 6'd50;
      56'b00000000000000000000000000000000000000000000000000001???: s3t_nlz = 6'd51;
      56'b000000000000000000000000000000000000000000000000000001??: s3t_nlz = 6'd52;
      56'b0000000000000000000000000000000000000000000000000000001?: s3t_nlz = 6'd53;
      56'b00000000000000000000000000000000000000000000000000000001: s3t_nlz = 6'd54;
      56'b00000000000000000000000000000000000000000000000000000000: s3t_nlz =  6'd0; // zero result
    endcase
  end // always

  // left shift amount and corrected exponent
  wire  [5:0] s3t_nlz_m1    = (s3t_nlz - 6'd1);
  wire [12:0] s3t_exp13c_m1 = s2o_exp13c - 13'd1;
  wire [12:0] s3t_exp13c_mz = s2o_exp13c - {7'd0,s3t_nlz};
  wire  [5:0] s3t_shl;
  wire [12:0] s3t_exp13shl;
  assign {s3t_shl,s3t_exp13shl} =
      // shift isn't needed or impossible
    (~(|s3t_nlz) | (s2o_exp13c == 13'd1)) ?
                              {6'd0,s2o_exp13c} :
      // normalization is possible
    (s2o_exp13c >  s3t_nlz) ? {s3t_nlz,s3t_exp13c_mz} :
      // denormalized cases
    (s2o_exp13c == s3t_nlz) ? {s3t_nlz_m1,13'd1} :
                              {s3t_exp13c_m1[5:0],13'd1};

  // re-pack single precision result in LSBs for rounding
  // format: {extra_h-bit, h-bit, 52/23-fractional, rnd-hi-bit, rnd-lo-bit}
  //         overall 56 bits for double precision
  //                 27 bits for single precision
  wire [55:0] s3t_fract56 = s2o_op_fp64_arith ? (s3t_fract56_add) : ({29'd0,s3t_fract56_add[55:29]});

  // update sticky (mostly for re-packed single precision)
  wire s3t_sticky = s2o_sticky | ((~s2o_op_fp64_arith) & (|s3t_fract56_add[28:0]));

  // registering output
  always @(posedge clk) begin
    if (s3_adv) begin
      add_sign_o      <= s2o_signc;
      add_sub_0_o     <= s2o_sub_0; // MAROCCHINO_TODO: optimize ?
      add_shl_o       <= s3t_shl;
      add_exp13shl_o  <= s3t_exp13shl;
      add_exp13sh0_o  <= s2o_exp13c;
      add_fract57_o   <= {s3t_fract56,s3t_sticky};
    end // advance
  end // @clock

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
  end // @clock

endmodule // pfpu_addsub_marocchino
