/////////////////////////////////////////////////////////////////////
//                                                                 //
//    pfpu_rnd_marocchino                                          //
//                                                                 //
//    32/64-bit common rounding module for                         //
//    MAROCCHINO's FPU                                             //
//                                                                 //
//    This file is part of the mor1kx project                      //
//    https://github.com/openrisc/mor1kx                           //
//                                                                 //
//    Author: Andrey Bacherov                                      //
//            avbacherov@opencores.org                             //
//                                                                 //
/////////////////////////////////////////////////////////////////////
//                                                                 //
//   Copyright (C) 2016-2018 Andrey Bacherov                       //
//                           avbacherov@opencores.org              //
//                                                                 //
//   This source file may be used and distributed without          //
//   restriction provided that this copyright statement is not     //
//   removed from the file and that any derivative work contains   //
//   the original copyright notice and the associated disclaimer.  //
//                                                                 //
//       THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY       //
//   EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     //
//   TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS     //
//   FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL THE AUTHOR        //
//   OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,           //
//   INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES      //
//   (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     //
//   GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR          //
//   BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF    //
//   LIABILITY, WHETHER IN  CONTRACT, STRICT LIABILITY, OR TORT    //
//   (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    //
//   OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE           //
//   POSSIBILITY OF SUCH DAMAGE.                                   //
//                                                                 //
/////////////////////////////////////////////////////////////////////

`include "mor1kx-defines.v"

module pfpu_rnd_marocchino
(
  // clocks, resets
  input                             cpu_clk,
  // pipe controls
  input                             pipeline_flush_i,
  output                            rnd_taking_add_o,
  output                            rnd_taking_mul_o,
  output                            rnd_taking_div_o,
  output                            rnd_taking_i2f_o,
  output                            rnd_taking_f2i_o,
  output reg                        fpxx_arith_valid_o,
  input                             padv_wrbk_i,
  input                             grant_wrbk_to_fpxx_arith_i,
  // configuration
  input                             rm_nearest_i,
  input                             rm_to_infp_i,
  input                             rm_to_infm_i,
  input                             except_fpu_enable_i,
  input [`OR1K_FPCSR_ALLF_SIZE-1:0] fpu_mask_flags_i,
  // input from add/sub
  input        add_rdy_i,       // add/sub is ready
  input        add_sign_i,      // add/sub signum
  input        add_sub_0_i,     // flag that actual substruction is performed and result is zero
  input        add_shr_i,       // do right shift in align stage
  input [12:0] add_exp13shr_i,  // exponent for right shift align
  input  [5:0] add_shl_i,       // do left shift in align stage
  input [12:0] add_exp13shl_i,  // exponent for left shift align
  input [12:0] add_exp13sh0_i,  // exponent for no shift in align
  input [56:0] add_fract57_i,   // fractional with appended {r,s} bits
  // input from mul
  input        mul_rdy_i,       // mul is ready
  input        mul_sign_i,      // mul signum
  input  [5:0] mul_shr_i,       // do right shift in align stage
  input [12:0] mul_exp13shr_i,  // exponent for right shift align
  input [12:0] mul_exp13sh0_i,  // exponent for no shift in align
  input [56:0] mul_fract57_i,   // fractional with appended {r,s} bits
  // input from div
  input        div_rdy_i,       // div is ready
  input        div_sign_i,      // signum
  input  [5:0] div_shr_i,       // do right shift in align stage
  input [12:0] div_exp13shr_i,  // exponent for right shift align
  input        div_shl_i,       // do left shift in align stage
  input [12:0] div_exp13shl_i,  // exponent for left shift align
  input [12:0] div_exp13sh0_i,  // exponent for no shift in align
  input [56:0] div_fract57_i,   // fractional with appended {r,s} bits
  input        div_dbz_i,       // div division by zero flag
  // input from i2f
  input        i2f_rdy_i,       // i2f is ready
  input        i2f_sign_i,      // i2f signum
  input  [3:0] i2f_shr_i,
  input [10:0] i2f_exp11shr_i,
  input  [5:0] i2f_shl_i,
  input [10:0] i2f_exp11shl_i,
  input [10:0] i2f_exp11sh0_i,
  input [63:0] i2f_fract64_i,
  // input from f2i
  input        f2i_rdy_i,       // f2i is ready
  input        f2i_sign_i,      // f2i signum
  input [52:0] f2i_int53_i,     // f2i fractional
  input  [5:0] f2i_shr_i,       // f2i required shift right value
  input  [3:0] f2i_shl_i,       // f2i required shift left value
  input        f2i_ovf_i,       // f2i overflow flag
  // from order control buffer
  input        rnd_op_fp64_arith_i,
  input        ocb_inv_i,
  input        ocb_inf_i,
  input        ocb_snan_i,
  input        ocb_qnan_i,
  input        ocb_anan_sign_i,
  // pre-Write-Back output
  output                                 exec_except_fpxx_arith_o, // generate exception
  // output Write-Back latches
  output reg                      [31:0] wrbk_fpxx_arith_res_hi_o,   // result
  output reg                      [31:0] wrbk_fpxx_arith_res_lo_o,   // result
  output reg [`OR1K_FPCSR_ALLF_SIZE-1:0] wrbk_fpxx_arith_fpcsr_o,    // fp64 arithmetic flags
  output reg                             wrbk_fpxx_arith_fpcsr_we_o, // update FPCSR
  output reg                             wrbk_except_fpxx_arith_o    // generate exception
);

  // constants for double precision
  localparam [62:0] INF_D  = 63'b111111111110000000000000000000000000000000000000000000000000000;
  localparam [62:0] QNAN_D = 63'b111111111111000000000000000000000000000000000000000000000000000;
  localparam [62:0] SNAN_D = 63'b111111111110111111111111111111111111111111111111111111111111111;

  // constants for single precision
  localparam [30:0] INF_S  = 31'b1111111100000000000000000000000;
  localparam [30:0] QNAN_S = 31'b1111111110000000000000000000000;
  localparam [30:0] SNAN_S = 31'b1111111101111111111111111111111;

  // Bit-reverse on left shift, perform right shift,
  // bit-reverse result on left shift.
  function [66:0] reverse67_pfpu_rnd;
  input [66:0] in;
  integer      i1;
  begin
    for (i1 = 0; i1 < 67; i1 = i1 + 1) begin
      reverse67_pfpu_rnd[66-i1] = in[i1];
    end
  end
  endfunction


  /*
     Any stage's output is registered.
     Definitions:
       s??o_name - "S"tage number "??", "O"utput
       s??t_name - "S"tage number "??", "T"emporary (internally)
  */


  // rounding pipe controls
  //  ## resdy flags of stages
  reg s0o_ready;
  reg s1o_ready;
  reg s2o_ready;
  reg s3o_ready;
  reg wrbk_fpxx_arith_miss_r;
  //  ## per stage busy flags
  wire s3_busy = s3o_ready & wrbk_fpxx_arith_miss_r;
  wire s2_busy = s2o_ready & s3_busy;
  wire s1_busy = s1o_ready & s2_busy;
  wire s0_busy = s0o_ready & s1_busy;
  //  ## per stage advance
  wire s0_adv  = (add_rdy_i | mul_rdy_i | div_rdy_i | i2f_rdy_i | f2i_rdy_i) & ~s0_busy;
  wire s1_adv  = s0o_ready & ~s1_busy;
  wire s2_adv  = s1o_ready & ~s2_busy;
  wire s3_adv  = s2o_ready & ~s3_busy;
  // ## per execution unit reporting
  assign rnd_taking_add_o = add_rdy_i & ~s0_busy;
  assign rnd_taking_mul_o = mul_rdy_i & ~s0_busy;
  assign rnd_taking_div_o = div_rdy_i & ~s0_busy;
  assign rnd_taking_i2f_o = i2f_rdy_i & ~s0_busy;
  assign rnd_taking_f2i_o = f2i_rdy_i & ~s0_busy;


  /* Stage #0: multiplexing */

  wire        s0t_sign;
  wire [66:0] s0t_fract67;
  wire        s0t_inv;
  wire        s0t_inf;
  wire        s0t_snan;
  wire        s0t_qnan;
  wire        s0t_anan_sign;

  // multiplexer for signums and flags
  wire s0t_add_sign = add_sub_0_i ? rm_to_infm_i : add_sign_i;

  assign s0t_sign = (add_rdy_i & s0t_add_sign) |
                    (mul_rdy_i & mul_sign_i)   |
                    (div_rdy_i & div_sign_i)   |
                    (f2i_rdy_i & f2i_sign_i)   |
                    (i2f_rdy_i & i2f_sign_i);

  // multiplexer for fractionals
  assign s0t_fract67 =
    ({67{add_rdy_i}} & {10'd0, add_fract57_i}) |
    ({67{mul_rdy_i}} & {10'd0, mul_fract57_i}) |
    ({67{div_rdy_i}} & {10'd0, div_fract57_i}) |
    ({67{f2i_rdy_i}} & {11'd0, f2i_int53_i,  3'd0}) |
    ({67{i2f_rdy_i}} & {       i2f_fract64_i,3'd0});

  // multiplexer for shift values
  wire  [5:0] s0t_shr;
  wire  [5:0] s0t_shl;
  // ---
  assign {s0t_shr, s0t_shl} =
    ({12{add_rdy_i}} & {{5'd0,add_shr_i},        add_shl_i}) |
    ({12{mul_rdy_i}} & {       mul_shr_i,             6'd0}) |
    ({12{div_rdy_i}} & {       div_shr_i, {5'd0,div_shl_i}}) |
    ({12{f2i_rdy_i}} & {       f2i_shr_i, {2'b0,f2i_shl_i}}) |
    ({12{i2f_rdy_i}} & {{2'b0,i2f_shr_i},       i2f_shl_i});
  // ---
  wire s0t_is_shr = (|s0t_shr);
  wire s0t_is_shl = (|s0t_shl);
  // ---
  wire [5:0] s0t_sh6 = s0t_is_shr ? s0t_shr :
                       s0t_is_shl ? s0t_shl : 6'd0;

  // two stage multiplexer for exponents
  wire [12:0] s0t_exp13shr;
  wire [12:0] s0t_exp13shl;
  wire [12:0] s0t_exp13sh0;
  // ---
  assign {s0t_exp13shr, s0t_exp13shl, s0t_exp13sh0} =
    ({39{add_rdy_i}} & {add_exp13shr_i, add_exp13shl_i, add_exp13sh0_i}) |
    ({39{mul_rdy_i}} & {mul_exp13shr_i,          13'd0, mul_exp13sh0_i}) |
    ({39{div_rdy_i}} & {div_exp13shr_i, div_exp13shl_i, div_exp13sh0_i}) |
    ({39{f2i_rdy_i}} & {         13'd0,          13'd0,          13'd0}) |
    ({39{i2f_rdy_i}} & {{2'd0,i2f_exp11shr_i},{2'd0,i2f_exp11shl_i},{2'd0,i2f_exp11sh0_i}});

  wire [12:0] s0t_exp13 = s0t_is_shr ? s0t_exp13shr :
                          s0t_is_shl ? s0t_exp13shl : s0t_exp13sh0;

  // stage #0 output registers
  reg         s0o_sign;
  reg         s0o_is_shr;
  reg   [5:0] s0o_shr;    // for correct computation of sticky
  reg   [5:0] s0o_shl;    // for correct computation of sticky
  reg   [5:0] s0o_sh6;    // for shift
  reg  [12:0] s0o_exp13;
  reg  [66:0] s0o_fract67;
  reg         s0o_op_fp64_arith;
  // various flags:
  reg         s0o_inv;
  reg         s0o_inf;
  reg         s0o_snan;
  reg         s0o_qnan;
  reg         s0o_anan_sign;
  // DIV specials
  reg         s0o_div_op;
  reg         s0o_div_dbz;
  // F2I specials
  reg         s0o_f2i;
  reg         s0o_f2i_sign;
  reg         s0o_f2i_ovf;
  // ---
  always @(posedge cpu_clk) begin
    if (s0_adv) begin
      s0o_sign          <= s0t_sign;
      s0o_is_shr        <= s0t_is_shr;
      s0o_shr           <= s0t_shr;
      s0o_shl           <= s0t_shl;
      s0o_sh6           <= s0t_sh6;
      s0o_exp13         <= s0t_exp13;
      s0o_fract67       <= s0t_is_shr ? s0t_fract67 : reverse67_pfpu_rnd(s0t_fract67);
      s0o_op_fp64_arith <= rnd_op_fp64_arith_i;
      // various flags:
      s0o_inv           <= ocb_inv_i;
      s0o_inf           <= ocb_inf_i;
      s0o_snan          <= ocb_snan_i;
      s0o_qnan          <= ocb_qnan_i;
      s0o_anan_sign     <= ocb_anan_sign_i;
      // DIV specials
      s0o_div_op        <= div_rdy_i;
      s0o_div_dbz       <= div_dbz_i;
      // F2I specials
      s0o_f2i           <= f2i_rdy_i;
      s0o_f2i_sign      <= f2i_sign_i;
      s0o_f2i_ovf       <= f2i_ovf_i;
    end
  end // @cpu-clock

  // ready is special case
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      s0o_ready <= 1'b0;
    else if (s0_adv)
      s0o_ready <= 1'b1;
    else if (s1_adv)
      s0o_ready <= 1'b0;
  end // @clock


  /* Stage #1: common align */

  // align
  wire [66:0] s1t_fract67shr = (s0o_fract67 >> s0o_sh6);
  wire [66:0] s1t_fract67sh  = s0o_is_shr ? s1t_fract67shr : reverse67_pfpu_rnd(s1t_fract67shr);

  // update sticky bit for right shift case.
  //  # select bits for sticky computation
  //    double/single fractionals are right (by LSB) aligned
  wire [56:0] s1t_fract57 = s0o_fract67[56:0];
  //  # maximum right shift value for  I2F is:
  //      11 in double precision case
  //       8 in single precision case
  reg s1r_sticky;
  always @(s1t_fract57 or s0o_shr) begin
    // synthesis parallel_case
    case (s0o_shr)
      6'd0   : s1r_sticky = |s1t_fract57[ 1:0];
      6'd1   : s1r_sticky = |s1t_fract57[ 2:0];
      6'd2   : s1r_sticky = |s1t_fract57[ 3:0];
      6'd3   : s1r_sticky = |s1t_fract57[ 4:0];
      6'd4   : s1r_sticky = |s1t_fract57[ 5:0];
      6'd5   : s1r_sticky = |s1t_fract57[ 6:0];
      6'd6   : s1r_sticky = |s1t_fract57[ 7:0];
      6'd7   : s1r_sticky = |s1t_fract57[ 8:0];
      6'd8   : s1r_sticky = |s1t_fract57[ 9:0];
      6'd9   : s1r_sticky = |s1t_fract57[10:0];
      6'd10  : s1r_sticky = |s1t_fract57[11:0];
      6'd11  : s1r_sticky = |s1t_fract57[12:0];
      6'd12  : s1r_sticky = |s1t_fract57[13:0];
      6'd13  : s1r_sticky = |s1t_fract57[14:0];
      6'd14  : s1r_sticky = |s1t_fract57[15:0];
      6'd15  : s1r_sticky = |s1t_fract57[16:0];
      6'd16  : s1r_sticky = |s1t_fract57[17:0];
      6'd17  : s1r_sticky = |s1t_fract57[18:0];
      6'd18  : s1r_sticky = |s1t_fract57[19:0];
      6'd19  : s1r_sticky = |s1t_fract57[20:0];
      6'd20  : s1r_sticky = |s1t_fract57[21:0];
      6'd21  : s1r_sticky = |s1t_fract57[22:0];
      6'd22  : s1r_sticky = |s1t_fract57[23:0];
      6'd23  : s1r_sticky = |s1t_fract57[24:0];
      6'd24  : s1r_sticky = |s1t_fract57[25:0];
      6'd25  : s1r_sticky = |s1t_fract57[26:0];
      6'd26  : s1r_sticky = |s1t_fract57[27:0];
      6'd27  : s1r_sticky = |s1t_fract57[28:0];
      6'd28  : s1r_sticky = |s1t_fract57[29:0];
      6'd29  : s1r_sticky = |s1t_fract57[30:0];
      6'd30  : s1r_sticky = |s1t_fract57[31:0];
      6'd31  : s1r_sticky = |s1t_fract57[32:0];
      6'd32  : s1r_sticky = |s1t_fract57[33:0];
      6'd33  : s1r_sticky = |s1t_fract57[34:0];
      6'd34  : s1r_sticky = |s1t_fract57[35:0];
      6'd35  : s1r_sticky = |s1t_fract57[36:0];
      6'd36  : s1r_sticky = |s1t_fract57[37:0];
      6'd37  : s1r_sticky = |s1t_fract57[38:0];
      6'd38  : s1r_sticky = |s1t_fract57[39:0];
      6'd39  : s1r_sticky = |s1t_fract57[40:0];
      6'd40  : s1r_sticky = |s1t_fract57[41:0];
      6'd41  : s1r_sticky = |s1t_fract57[42:0];
      6'd42  : s1r_sticky = |s1t_fract57[43:0];
      6'd43  : s1r_sticky = |s1t_fract57[44:0];
      6'd44  : s1r_sticky = |s1t_fract57[45:0];
      6'd45  : s1r_sticky = |s1t_fract57[46:0];
      6'd46  : s1r_sticky = |s1t_fract57[47:0];
      6'd47  : s1r_sticky = |s1t_fract57[48:0];
      6'd48  : s1r_sticky = |s1t_fract57[49:0];
      6'd49  : s1r_sticky = |s1t_fract57[50:0];
      6'd50  : s1r_sticky = |s1t_fract57[51:0];
      6'd51  : s1r_sticky = |s1t_fract57[52:0];
      6'd52  : s1r_sticky = |s1t_fract57[53:0];
      6'd53  : s1r_sticky = |s1t_fract57[54:0];
      6'd54  : s1r_sticky = |s1t_fract57[55:0];
      default: s1r_sticky = |s1t_fract57;
    endcase
  end // always

  // update sticky bit for left shift case
  //    double/single fractionals are right (by LSB) aligned
  wire [1:0] s1t_fract2 = {s0o_fract67[65],s0o_fract67[66]}; // it is reversed for left shift
  // ---
  reg s1l_sticky;
  always @(s1t_fract2 or s0o_shl) begin
    // synthesis parallel_case
    case (s0o_shl)
      5'd0   : s1l_sticky = |s1t_fract2;
      5'd1   : s1l_sticky =  s1t_fract2[0];
      default: s1l_sticky = 1'b0;
    endcase
  end // always

  wire s1t_sticky = s0o_is_shr ? s1r_sticky : s1l_sticky;

  // output of align stage
  reg        s1o_sign;
  reg [12:0] s1o_exp13;
  reg [63:0] s1o_fract64;
  reg  [1:0] s1o_rs;
  reg        s1o_op_fp64_arith;
  reg        s1o_inv;
  reg        s1o_inf;
  reg        s1o_snan;
  reg        s1o_qnan;
  reg        s1o_anan_sign;
  // DIV specials
  reg        s1o_div_op, s1o_div_dbz;
  // F2I specials
  reg        s1o_f2i;
  reg        s1o_f2i_sign;
  reg        s1o_f2i_sign_cp;
  reg        s1o_f2i_ovf;
  reg        s1o_op_fp64_f2i;
  // registering
  always @(posedge cpu_clk) begin
    if(s1_adv) begin
      s1o_sign          <= s0o_sign;
      s1o_exp13         <= s0o_exp13;
      s1o_fract64       <= s1t_fract67sh[66:3];
      s1o_rs            <= {s1t_fract67sh[2],s1t_sticky};
      s1o_op_fp64_arith <= s0o_op_fp64_arith;
      // various flags:
      s1o_inv           <= s0o_inv;
      s1o_inf           <= s0o_inf;
      s1o_snan          <= s0o_snan;
      s1o_qnan          <= s0o_qnan;
      s1o_anan_sign     <= s0o_anan_sign;
      // DIV specials
      s1o_div_op        <= s0o_div_op;
      s1o_div_dbz       <= s0o_div_dbz;
      // F2I specials
      s1o_f2i           <= s0o_f2i;
      s1o_f2i_sign      <= s0o_f2i_sign; // copy for P&R
      s1o_f2i_sign_cp   <= s0o_f2i_sign; // copy for P&R
      s1o_f2i_ovf       <= s0o_f2i_ovf;
      s1o_op_fp64_f2i   <= s0o_op_fp64_arith; // copy for P&R
    end // advance
  end // @clock

  // ready is special case
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      s1o_ready <= 1'b0;
    else if (s1_adv)
      s1o_ready <= 1'b1;
    else if (s2_adv)
      s1o_ready <= 1'b0;
  end // @clock


  /* Stage #2: rounding */


  wire s2t_g    = s1o_fract64[0];
  wire s2t_r    = s1o_rs[1];
  wire s2t_s    = s1o_rs[0];
  wire s2t_lost = s2t_r | s2t_s;

  wire s2t_rnd_up = (rm_nearest_i & s2t_r & s2t_s) |
                    (rm_nearest_i & s2t_g & s2t_r & (~s2t_s)) |
                    (rm_to_infp_i & (~s1o_sign) & s2t_lost) |
                    (rm_to_infm_i &   s1o_sign  & s2t_lost);

  // IEEE compliance rounding for qutient
  wire s2t_div_rnd_up = (rm_nearest_i & s2t_r & s2t_s) |
                        (rm_to_infp_i & (~s1o_sign) & s2t_s) |
                        (rm_to_infm_i &   s1o_sign  & s2t_s);

  // set resulting direction of rounding
  //  a) normalized quotient is rounded by quotient related rules
  //  b) de-normalized quotient is rounded by common rules
  wire s2t_rnd_n_qtnt = s1o_div_op & (s1o_op_fp64_arith ? s1o_fract64[52] : s1o_fract64[23]); // normalized quotient
  wire s2t_set_rnd_up = s2t_rnd_n_qtnt ? s2t_div_rnd_up : s2t_rnd_up;

  // rounded fractional
  wire [63:0] s2t_fract64_rnd = s1o_fract64 + {63'd0,s2t_set_rnd_up};

  // rounding analysis for F2I further processing
  //  # F2I invalid result (overflow)
  wire s2t_f2i_carry_rnd = s1o_op_fp64_f2i ? s2t_fract64_rnd[63] : s2t_fract64_rnd[31];
  wire s2t_f2i_inv       = ((~s1o_f2i_sign) & s2t_f2i_carry_rnd) | s1o_f2i_ovf;
  //  # prepare to tow's complement conversion (left aligned)
  //  #  if invalid (i.e. overflow) return maximum signed integer
  wire [63:0] s2t_int64_rnd;
  assign s2t_int64_rnd = {64{s1o_f2i_sign_cp}} ^
                         (s2t_f2i_inv ? 64'h7fffffffffffffff :
                           (s1o_op_fp64_f2i ? s2t_fract64_rnd :
                                              {s2t_fract64_rnd[31:0],32'd0}));

  // output of rounding stage
  reg        s2o_sign;
  reg [12:0] s2o_exp13;
  reg [63:0] s2o_fract64_rnd;
  reg        s2o_lost;
  reg        s2o_op_fp64_arith;
  reg        s2o_inv;
  reg        s2o_inf;
  reg        s2o_snan;
  reg        s2o_qnan;
  reg        s2o_anan_sign;
  // DIV specials
  reg        s2o_dbz;
  // F2I specials
  reg        s2o_f2i;
  reg        s2o_f2i_sign;
  reg        s2o_f2i_inv;
  reg [63:0] s2o_int64_rnd;
  // registering
  always @(posedge cpu_clk) begin
    if(s2_adv) begin
      s2o_sign          <= s1o_sign;
      s2o_exp13         <= s1o_exp13;
      s2o_fract64_rnd   <= s2t_fract64_rnd;
      s2o_lost          <= s2t_lost;
      s2o_op_fp64_arith <= s1o_op_fp64_arith;
      // various flags:
      s2o_inv           <= s1o_inv;
      s2o_inf           <= s1o_inf;
      s2o_snan          <= s1o_snan;
      s2o_qnan          <= s1o_qnan;
      s2o_anan_sign     <= s1o_anan_sign;
      // DIV specials
      s2o_dbz           <= s1o_div_dbz;
      // F2I specials
      s2o_f2i           <= s1o_f2i;
      s2o_f2i_sign      <= (~s2t_f2i_inv) & s1o_f2i_sign;
      s2o_f2i_inv       <= s2t_f2i_inv;
      s2o_int64_rnd     <= s2t_int64_rnd;
    end // advance
  end // @clock

  // ready is special case
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      s2o_ready <= 1'b0;
    else if (s2_adv)
      s2o_ready <= 1'b1;
    else if (s3_adv)
      s2o_ready <= 1'b0;
  end // @clock


  /* Stage #3: final align */


  // floating point output
  wire s3t_fxx_shr = s2o_op_fp64_arith ? s2o_fract64_rnd[53] : s2o_fract64_rnd[24];
  // update exponent and fraction
  wire [12:0] s3t_fxx_exp13   = s2o_exp13 + {12'd0,s3t_fxx_shr};
  wire [52:0] s3t_fxx_fract53 = s3t_fxx_shr ? s2o_fract64_rnd[53:1] :
                                              s2o_fract64_rnd[52:0];
  // denormalized or zero
  wire s3t_fxx_fract53_dn = s2o_op_fp64_arith ? (~s3t_fxx_fract53[52]) : (~s3t_fxx_fract53[23]);
  // floating point overflow and infinity
  wire s3t_fxx_ovf = (s3t_fxx_exp13 > (s2o_op_fp64_arith ? 13'd2046 : 13'd254)) | s2o_inf | s2o_dbz;


  // F2I complete conversion to two's complement
  //  # left aligned
  //  # maximum signed value if overflaw
  wire [63:0] s3t_ixx_opc = s2o_int64_rnd + {63'd0,s2o_f2i_sign};
  // zero flag
  wire s3t_ixx_00 = (~s2o_f2i_inv) & (~(|s2o_fract64_rnd));


  // output of final align stage
  reg         s3o_sign;
  reg         s3o_lost;
  reg         s3o_op_fp64_arith;
  // various flags:
  reg         s3o_inv;
  reg         s3o_inf;
  reg         s3o_snan;
  reg         s3o_qnan;
  reg         s3o_anan_sign;
  // FP3264
  reg  [12:0] s3o_fxx_exp13;
  reg  [52:0] s3o_fxx_fract53;
  reg         s3o_fxx_fract53_dn;
  reg         s3o_fxx_ovf;
  // DIV specials
  reg         s3o_dbz;
  // F2I specials
  reg         s3o_f2i;
  reg         s3o_f2i_inv;
  reg  [63:0] s3o_ixx_opc;
  reg         s3o_ixx_00;
  // registering
  always @(posedge cpu_clk) begin
    if(s3_adv) begin
      s3o_sign            <= s2o_sign;
      s3o_lost            <= s2o_lost;
      s3o_op_fp64_arith   <= s2o_op_fp64_arith;
      // various flags:
      s3o_inv             <= s2o_inv;
      s3o_inf             <= s2o_inf;
      s3o_snan            <= s2o_snan;
      s3o_qnan            <= s2o_qnan;
      s3o_anan_sign       <= s2o_anan_sign;
      // FP3264
      s3o_fxx_exp13       <= s3t_fxx_exp13;
      s3o_fxx_fract53     <= s3t_fxx_fract53;
      s3o_fxx_fract53_dn  <= s3t_fxx_fract53_dn;
      s3o_fxx_ovf         <= s3t_fxx_ovf;
      // DIV specials
      s3o_dbz             <= s2o_dbz;
      // F2I specials
      s3o_f2i             <= s2o_f2i;
      s3o_f2i_inv         <= s2o_f2i_inv;
      s3o_ixx_opc         <= s3t_ixx_opc;
      s3o_ixx_00          <= s3t_ixx_00;
    end // advance
  end // @clock

  // ready is special case
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      s3o_ready <= 1'b0;
    else if (s3_adv)
      s3o_ready <= 1'b1;
    else if (~wrbk_fpxx_arith_miss_r)
      s3o_ready <= 1'b0;
  end // @clock

  //  valid flag
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      fpxx_arith_valid_o <= 1'b0;
    else if (s3_adv)
      fpxx_arith_valid_o <= 1'b1;
    else if (padv_wrbk_i & grant_wrbk_to_fpxx_arith_i)
      fpxx_arith_valid_o <= wrbk_fpxx_arith_miss_r ? s3o_ready : 1'b0;
  end // @clock


  /* Stage #4: formatting result */


  // Multiplexing flags
  wire s4t_ine, s4t_ovf, s4t_inf, s4t_unf, s4t_zer;
  // ---
  assign {s4t_ine,s4t_ovf,s4t_inf,s4t_unf,s4t_zer} =
    // f2i          ine  ovf  inf  unf        zer
    s3o_f2i ? {s3o_lost,1'b0,1'b0,1'b0,s3o_ixx_00} :
    // qnan output            ine  ovf  inf  unf  zer
   ((s3o_snan | s3o_qnan) ? {1'b0,1'b0,1'b0,1'b0,1'b0} :
    // snan output            ine  ovf  inf  unf  zer
   (s3o_inv ?               {1'b0,1'b0,1'b0,1'b0,1'b0} :
    // overflow and infinity                          ine                       ovf  inf  unf  zer
   (s3o_fxx_ovf ? {((s3o_lost | (~s3o_inf)) & (~s3o_dbz)),((~s3o_inf) & (~s3o_dbz)),1'b1,1'b0,1'b0} :
    // denormalized or zero      ine  ovf  inf                             unf                 zer
   ((s3o_fxx_fract53_dn) ? {s3o_lost,1'b0,1'b0,(s3o_lost & s3o_fxx_fract53_dn),~(|s3o_fxx_fract53)} :
    // normal result             ine  ovf  inf  unf  zer
                           {s3o_lost,1'b0,1'b0,1'b0,1'b0}))));

  // Multiplexing double precision
  wire [63:0] s4t_opc64;
  assign s4t_opc64 =
    // f2i
    s3o_f2i ? s3o_ixx_opc :
    // qnan output
   ((s3o_snan | s3o_qnan) ? {s3o_anan_sign,QNAN_D} :
    // snan output
   (s3o_inv ? {s3o_sign,SNAN_D} :
    // overflow and infinity
   (s3o_fxx_ovf ? {s3o_sign,INF_D} :
    // denormalized or zero
   ((s3o_fxx_fract53_dn) ? {s3o_sign,11'd0,s3o_fxx_fract53[51:0]} :
    // normal result
                           {s3o_sign,s3o_fxx_exp13[10:0],s3o_fxx_fract53[51:0]}))));

  // Multiplexing single precision
  wire [31:0] s4t_opc32;
  assign s4t_opc32 =
    // f2i
    s3o_f2i ? s3o_ixx_opc[63:32] :
    // qnan output
   ((s3o_snan | s3o_qnan) ? {s3o_anan_sign,QNAN_S} :
    // snan output
   (s3o_inv ? {s3o_sign,SNAN_S} :
    // overflow and infinity
   (s3o_fxx_ovf ? {s3o_sign,INF_S} :
    // denormalized or zero
   ((s3o_fxx_fract53_dn) ? {s3o_sign,8'd0,s3o_fxx_fract53[22:0]} :
    // normal result
                           {s3o_sign,s3o_fxx_exp13[7:0],s3o_fxx_fract53[22:0]}))));


  // EXECUTE level FP32 arithmetic flags
  wire [`OR1K_FPCSR_ALLF_SIZE-1:0] s4t_fpxx_arith_fpcsr =
    {s3o_dbz, s4t_inf, (s3o_inv | (s3o_f2i_inv & s3o_f2i) | s3o_snan),
     s4t_ine, s4t_zer, s3o_qnan,
     (s3o_inv | (s3o_snan & s3o_f2i)), s4t_unf, s4t_ovf} & fpu_mask_flags_i;

  // EXEC-result #1
  wire [31:0] s4t_fpxx_arith_res_hi = s3o_op_fp64_arith ? s4t_opc64[63:32] : s4t_opc32;
  // EXEC-result #2
  wire [31:0] s4t_fpxx_arith_res_lo = s4t_opc64[31:0];


  // Write-Back-miss flag
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      wrbk_fpxx_arith_miss_r <= 1'b0;
    else if (padv_wrbk_i & grant_wrbk_to_fpxx_arith_i)
      wrbk_fpxx_arith_miss_r <= 1'b0;
    else if (~wrbk_fpxx_arith_miss_r)
      wrbk_fpxx_arith_miss_r <= s3o_ready;
  end // @clock

  // Write-Back-miss pending rezults
  reg [31:0] fpxx_arith_res_hi_p;
  reg [31:0] fpxx_arith_res_lo_p;
  reg [`OR1K_FPCSR_ALLF_SIZE-1:0] fpxx_arith_fpcsr_we_p;
  // ---
  always @(posedge cpu_clk) begin
    if (~wrbk_fpxx_arith_miss_r) begin
      fpxx_arith_res_hi_p   <= s4t_fpxx_arith_res_hi;
      fpxx_arith_res_lo_p   <= s4t_fpxx_arith_res_lo;
      fpxx_arith_fpcsr_we_p <= s4t_fpxx_arith_fpcsr;
    end
  end // @clock

  // EXECUTE level FP32 arithmetic exception
  wire   mux_except_fpxx_arith    = (wrbk_fpxx_arith_miss_r ? (|fpxx_arith_fpcsr_we_p) : (|s4t_fpxx_arith_fpcsr)) & except_fpu_enable_i;
  assign exec_except_fpxx_arith_o = grant_wrbk_to_fpxx_arith_i & mux_except_fpxx_arith;

  // Write-Back: result
  wire [31:0] wrbk_fpxx_arith_res_hi_m = wrbk_fpxx_arith_miss_r ? fpxx_arith_res_hi_p : s4t_fpxx_arith_res_hi;
  wire [31:0] wrbk_fpxx_arith_res_lo_m = wrbk_fpxx_arith_miss_r ? fpxx_arith_res_lo_p : s4t_fpxx_arith_res_lo;
  // ---
  always @(posedge cpu_clk) begin
    if(padv_wrbk_i) begin
      if (grant_wrbk_to_fpxx_arith_i) begin
        wrbk_fpxx_arith_res_hi_o <= wrbk_fpxx_arith_res_hi_m;
        wrbk_fpxx_arith_res_lo_o <= wrbk_fpxx_arith_res_lo_m;
      end
      else begin
        wrbk_fpxx_arith_res_hi_o <= 32'd0;
        wrbk_fpxx_arith_res_lo_o <= 32'd0;
      end
    end // Write-Back-advance
  end // @clock

  // Write-Back: flags
  always @(posedge cpu_clk) begin
    if (padv_wrbk_i & grant_wrbk_to_fpxx_arith_i) begin
      wrbk_fpxx_arith_fpcsr_o    <= wrbk_fpxx_arith_miss_r ? fpxx_arith_fpcsr_we_p : s4t_fpxx_arith_fpcsr;
      wrbk_except_fpxx_arith_o   <= mux_except_fpxx_arith;
      wrbk_fpxx_arith_fpcsr_we_o <= 1'b1;
    end
    else begin
      wrbk_fpxx_arith_fpcsr_o    <= {`OR1K_FPCSR_ALLF_SIZE{1'b0}};
      wrbk_except_fpxx_arith_o   <= 1'b0;
      wrbk_fpxx_arith_fpcsr_we_o <= 1'b0;
    end
  end // @clock

endmodule // pfpu_rnd_marocchino
