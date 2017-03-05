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
//   Copyright (C) 2016 Andrey Bacherov                            //
//                      avbacherov@opencores.org                   //
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
  input                             clk,
  input                             rst,
  // pipe controls
  input                             pipeline_flush_i,
  output                            rnd_taking_add_o,
  output                            rnd_taking_mul_o,
  output                            rnd_taking_div_o,
  output                            rnd_taking_i2f_o,
  output                            rnd_taking_f2i_o,
  output                            fpxx_arith_valid_o,
  input                             padv_wb_i,
  input                             grant_wb_to_fpxx_arith_i,
  // configuration
  input                       [1:0] rmode_i,  // rounding mode
  input                             except_fpu_enable_i,
  input [`OR1K_FPCSR_ALLF_SIZE-1:0] ctrl_fpu_mask_flags_i,
  // input from add/sub
  input        add_rdy_i,       // add/sub is ready
  input        add_sign_i,      // add/sub signum
  input        add_sub_0_i,     // flag that actual substruction is performed and result is zero
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
  // pre-WB output
  output                                 exec_except_fpxx_arith_o, // generate exception
  // output WB latches
  output reg                      [31:0] wb_fpxx_arith_res_hi_o,   // result
  output reg                      [31:0] wb_fpxx_arith_res_lo_o,   // result
  output reg [`OR1K_FPCSR_ALLF_SIZE-1:0] wb_fpxx_arith_fpcsr_o,    // fp64 arithmetic flags
  output reg                             wb_fpxx_arith_wb_fpcsr_o, // update FPCSR
  output reg                             wb_except_fpxx_arith_o    // generate exception
);

  // constants for double precision
  localparam INF_D  = 63'b111111111110000000000000000000000000000000000000000000000000000;
  localparam QNAN_D = 63'b111111111111000000000000000000000000000000000000000000000000000;
  localparam SNAN_D = 63'b111111111110111111111111111111111111111111111111111111111111111;

  // constants for single precision
  localparam INF_S  = 31'b1111111100000000000000000000000;
  localparam QNAN_S = 31'b1111111110000000000000000000000;
  localparam SNAN_S = 31'b1111111101111111111111111111111;


  // rounding mode isn't require pipelinization
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


  // rounding pipe controls
  //  ## resdy flags of stages
  reg s1o_ready;
  //  ## per stage busy flags
  wire s1_busy = s1o_ready & ~(padv_wb_i & grant_wb_to_fpxx_arith_i);
  //  ## per stage advance
  wire s1_adv  = (add_rdy_i | mul_rdy_i | div_rdy_i | i2f_rdy_i | f2i_rdy_i) & ~s1_busy;
  // ## per execution unit reporting
  assign rnd_taking_add_o = add_rdy_i & ~s1_busy;
  assign rnd_taking_mul_o = mul_rdy_i & ~s1_busy;
  assign rnd_taking_div_o = div_rdy_i & ~s1_busy;
  assign rnd_taking_i2f_o = i2f_rdy_i & ~s1_busy;
  assign rnd_taking_f2i_o = f2i_rdy_i & ~s1_busy;

  // output of rounding pipe state
  assign fpxx_arith_valid_o = s1o_ready;


  /* Stage #1: common align */

  wire        s1t_sign;
  wire [66:0] s1t_fract67;
  wire        s1t_inv;
  wire        s1t_inf;
  wire        s1t_snan;
  wire        s1t_qnan;
  wire        s1t_anan_sign;
  wire  [5:0] s1t_shr;
  wire  [5:0] s1t_shl;

  // multiplexer for signums and flags
  wire s1t_add_sign = add_sub_0_i ? rm_to_infm : add_sign_i;

  assign s1t_sign = (add_rdy_i & s1t_add_sign) |
                    (mul_rdy_i & mul_sign_i)   |
                    (div_rdy_i & div_sign_i)   |
                    (f2i_rdy_i & f2i_sign_i)   |
                    (i2f_rdy_i & i2f_sign_i);

  // multiplexer for fractionals
  assign s1t_fract67 =
    ({67{add_rdy_i}} & {10'd0, add_fract57_i}) |
    ({67{mul_rdy_i}} & {10'd0, mul_fract57_i}) |
    ({67{div_rdy_i}} & {10'd0, div_fract57_i}) |
    ({67{f2i_rdy_i}} & {11'd0, f2i_int53_i,  3'd0}) |
    ({67{i2f_rdy_i}} & {       i2f_fract64_i,3'd0});

  // overflow bit for add/mul
  // MAROCCHINO_TODO: optimize ?
  wire s1t_addmul_carry = (add_rdy_i & (rnd_op_fp64_arith_i ? add_fract57_i[56] : add_fract57_i[27])) |
                          (mul_rdy_i & (rnd_op_fp64_arith_i ? mul_fract57_i[56] : mul_fract57_i[27]));

  // multiplexer for shift values
  wire [5:0] s1t_shr_t;
  assign {s1t_shr_t, s1t_shl} =
    ({12{add_rdy_i}} & {            6'd0,        add_shl_i}) |  // MAROCCHINO_TODO: optimize right shift ?
    ({12{mul_rdy_i}} & {       mul_shr_i,             6'd0}) |  // MAROCCHINO_TODO: optimize right shift ?
    ({12{div_rdy_i}} & {       div_shr_i, {5'd0,div_shl_i}}) |
    ({12{f2i_rdy_i}} & {       f2i_shr_i, {2'b0,f2i_shl_i}}) |
    ({12{i2f_rdy_i}} & {{2'b0,i2f_shr_i},       i2f_shl_i});

  assign s1t_shr = (|s1t_shr_t) ? s1t_shr_t : {5'd0,s1t_addmul_carry};  // MAROCCHINO_TODO: optimize ?

  // align
  wire [66:0] s1t_fract67sh = (|s1t_shr) ? (s1t_fract67 >> s1t_shr) :
                                           (s1t_fract67 << s1t_shl);

  // update sticky bit for right shift case.
  //  # select bits for sticky computation
  //    double/single fractionals are right (by LSB) aligned
  wire [56:0] s1t_fract57 = s1t_fract67[56:0];
  //  # maximum right shift value for  I2F is:
  //      11 in double precision case
  //       8 in single precision case
  reg s1r_sticky;
  always @(s1t_fract57 or s1t_shr) begin
    // synthesis parallel_case full_case
    case (s1t_shr)
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
  wire [1:0] s1t_fract2 = s1t_fract67[1:0];
  // ---
  reg s1l_sticky;
  always @(s1t_fract2 or s1t_shl) begin
    // synthesis parallel_case full_case
    case (s1t_shl)
      5'd0   : s1l_sticky = |s1t_fract2;
      5'd1   : s1l_sticky =  s1t_fract2[0];
      default: s1l_sticky = 1'b0;
    endcase
  end // always

  wire s1t_sticky = (|s1t_shr) ? s1r_sticky : s1l_sticky;

  // two stage multiplexer for exponents
  wire [12:0] s1t_exp13shr;
  wire [12:0] s1t_exp13shl;
  wire [12:0] s1t_exp13sh0;
  assign {s1t_exp13shr, s1t_exp13shl, s1t_exp13sh0} =
    ({39{add_rdy_i}} & {add_exp13sh0_i, add_exp13shl_i, add_exp13sh0_i}) |
    ({39{mul_rdy_i}} & {mul_exp13shr_i,          13'd0, mul_exp13sh0_i}) |
    ({39{div_rdy_i}} & {div_exp13shr_i, div_exp13shl_i, div_exp13sh0_i}) |
    ({39{f2i_rdy_i}} & {         13'd0,          13'd0,          13'd0}) |
    ({39{i2f_rdy_i}} & {{2'd0,i2f_exp11shr_i},{2'd0,i2f_exp11shl_i},{2'd0,i2f_exp11sh0_i}});

  wire [12:0] s1t_exp13 =
    (|s1t_shr_t)  ? s1t_exp13shr :
    (~(|s1t_shl)) ? (s1t_exp13sh0 + {12'd0,s1t_addmul_carry}) :
                    s1t_exp13shl;

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
  reg        s1o_div_op, s1o_div_dbz;
  reg        s1o_f2i_ovf, s1o_f2i;
  // registering
  always @(posedge clk) begin
    if(s1_adv) begin
      s1o_sign          <= s1t_sign;
      s1o_exp13         <= s1t_exp13;
      s1o_fract64       <= s1t_fract67sh[66:3];
      s1o_rs            <= {s1t_fract67sh[2],s1t_sticky};
      s1o_op_fp64_arith <= rnd_op_fp64_arith_i;
      // various flags:
      s1o_inv       <= ocb_inv_i;
      s1o_inf       <= ocb_inf_i;
      s1o_snan      <= ocb_snan_i;
      s1o_qnan      <= ocb_qnan_i;
      s1o_anan_sign <= ocb_anan_sign_i;
      // DIV specials
      s1o_div_op  <= div_rdy_i;
      s1o_div_dbz <= div_dbz_i;
      // I2F specials
      s1o_f2i_ovf <= f2i_ovf_i;
      s1o_f2i     <= f2i_rdy_i;
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
    else if (padv_wb_i & grant_wb_to_fpxx_arith_i)
      s1o_ready <= 1'b0;
  end // @clock


  /* Stage #2: rounding */


  wire s2t_dbz  = s1o_div_dbz; // MAROCCHINO_TODO: optimize ?

  wire s2t_g    = s1o_fract64[0];
  wire s2t_r    = s1o_rs[1];
  wire s2t_s    = s1o_rs[0];
  wire s2t_lost = s2t_r | s2t_s;

  wire s2t_rnd_up = (rm_nearest & s2t_r & s2t_s) |
                    (rm_nearest & s2t_g & s2t_r & (~s2t_s)) |
                    (rm_to_infp & (~s1o_sign) & s2t_lost) |
                    (rm_to_infm &   s1o_sign  & s2t_lost);

  // IEEE compliance rounding for qutient
  wire s2t_div_rnd_up = (rm_nearest & s2t_r & s2t_s) |
                        (rm_to_infp & (~s1o_sign) & s2t_s) |
                        (rm_to_infm &   s1o_sign  & s2t_s);

  // set resulting direction of rounding
  //  a) normalized quotient is rounded by quotient related rules
  //  b) de-normalized quotient is rounded by common rules
  wire s2t_rnd_n_qtnt = s1o_div_op & (s1o_op_fp64_arith ? s1o_fract64[52] : s1o_fract64[23]); // normalized quotient
  wire s2t_set_rnd_up = s2t_rnd_n_qtnt ? s2t_div_rnd_up : s2t_rnd_up;

  // rounded fractional
  wire [63:0] s2t_fract64_rnd = s1o_fract64 + {63'd0,s2t_set_rnd_up};


  // floating point output
  wire s2t_fxx_shr = s1o_op_fp64_arith ? s2t_fract64_rnd[53] : s2t_fract64_rnd[24];
  // update exponent and fraction
  wire [12:0] s2t_fxx_exp13   = s1o_exp13 + {12'd0,s2t_fxx_shr};
  wire [52:0] s2t_fxx_fract53 = s2t_fxx_shr ? s2t_fract64_rnd[53:1] :
                                              s2t_fract64_rnd[52:0];
  // denormalized or zero
  wire s2t_fxx_fract53_dn = s1o_op_fp64_arith ? (~s2t_fxx_fract53[52]) : (~s2t_fxx_fract53[23]);
  // floating point overflow and infinity
  wire s2t_fxx_ovf = (s2t_fxx_exp13 > (s1o_op_fp64_arith ? 13'd2046 : 13'd254)) | s1o_inf | s2t_dbz;


  // integer output (f2i)
  wire s2t_ixx_carry_rnd = s1o_op_fp64_arith ? s2t_fract64_rnd[63] : s2t_fract64_rnd[31];
  wire s2t_ixx_inv       = ((~s1o_sign) & s2t_ixx_carry_rnd) | s1o_f2i_ovf;
  // two's complement for negative number
  wire [63:0] s2t_ixx_value = (s2t_fract64_rnd ^ {64{s1o_sign}}) + {63'd0,s1o_sign};
  // zero
  wire s2t_ixx_value_00 = (~s2t_ixx_inv) & (~(|s2t_fract64_rnd));
  // maximum signed integer:
  //   i32/i64 are right aligned
  wire [63:0] s2t_ixx_max = s1o_op_fp64_arith ? (64'h7fffffffffffffff ^ {64{s1o_sign}}) :
                                                {32'd0,(32'h7fffffff ^ {32{s1o_sign}})};
  // int output
  wire [63:0] s2t_ixx_opc = s2t_ixx_inv ? s2t_ixx_max : s2t_ixx_value;


  // Multiplexing flags
  wire s2t_ine, s2t_ovf, s2t_inf, s2t_unf, s2t_zer;
  // ---
  assign {s2t_ine,s2t_ovf,s2t_inf,s2t_unf,s2t_zer} =
    // f2i          ine  ovf  inf  unf              zer
    s1o_f2i ? {s2t_lost,1'b0,1'b0,1'b0,s2t_ixx_value_00} :
    // qnan output            ine  ovf  inf  unf  zer
    (s1o_snan | s1o_qnan) ? {1'b0,1'b0,1'b0,1'b0,1'b0} :
    // snan output            ine  ovf  inf  unf  zer
    s1o_inv ?               {1'b0,1'b0,1'b0,1'b0,1'b0} :
    // overflow and infinity                          ine                       ovf  inf  unf  zer
    s2t_fxx_ovf ? {((s2t_lost | (~s1o_inf)) & (~s2t_dbz)),((~s1o_inf) & (~s2t_dbz)),1'b1,1'b0,1'b0} :
    // denormalized or zero      ine  ovf  inf                             unf                 zer
    (s2t_fxx_fract53_dn) ? {s2t_lost,1'b0,1'b0,(s2t_lost & s2t_fxx_fract53_dn),~(|s2t_fxx_fract53)} :
    // normal result             ine  ovf  inf  unf  zer
                           {s2t_lost,1'b0,1'b0,1'b0,1'b0};

  // Multiplexing double precision
  wire [63:0] s2t_opc64;
  assign s2t_opc64 =
    // f2i
    s1o_f2i ? s2t_ixx_opc :
    // qnan output
    (s1o_snan | s1o_qnan) ? {s1o_anan_sign,QNAN_D} :
    // snan output
    s1o_inv ? {s1o_sign,SNAN_D} :
    // overflow and infinity
    s2t_fxx_ovf ? {s1o_sign,INF_D} :
    // denormalized or zero
    (s2t_fxx_fract53_dn) ? {s1o_sign,11'd0,s2t_fxx_fract53[51:0]} :
    // normal result
                           {s1o_sign,s2t_fxx_exp13[10:0],s2t_fxx_fract53[51:0]};

  // Multiplexing single precision
  wire [31:0] s2t_opc32;
  assign s2t_opc32 =
    // f2i
    s1o_f2i ? s2t_ixx_opc[31:0] :
    // qnan output
    (s1o_snan | s1o_qnan) ? {s1o_anan_sign,QNAN_S} :
    // snan output
    s1o_inv ? {s1o_sign,SNAN_S} :
    // overflow and infinity
    s2t_fxx_ovf ? {s1o_sign,INF_S} :
    // denormalized or zero
    (s2t_fxx_fract53_dn) ? {s1o_sign,8'd0,s2t_fxx_fract53[22:0]} :
    // normal result
                           {s1o_sign,s2t_fxx_exp13[7:0],s2t_fxx_fract53[22:0]};


  // EXECUTE level FP32 arithmetic flags
  wire [`OR1K_FPCSR_ALLF_SIZE-1:0] exec_fpxx_arith_fpcsr =
    {s2t_dbz, s2t_inf, (s1o_inv | (s2t_ixx_inv & s1o_f2i) | s1o_snan),
     s2t_ine, s2t_zer, s1o_qnan,
     (s1o_inv | (s1o_snan & s1o_f2i)), s2t_unf, s2t_ovf} &
    ctrl_fpu_mask_flags_i & {`OR1K_FPCSR_ALLF_SIZE{grant_wb_to_fpxx_arith_i}};

  // EXECUTE level FP32 arithmetic exception
  assign exec_except_fpxx_arith_o = except_fpu_enable_i & (|exec_fpxx_arith_fpcsr);


  // WB: result
  always @(posedge clk) begin
    if(padv_wb_i) begin
      // for WB-result #1
      wb_fpxx_arith_res_hi_o <= (s1o_op_fp64_arith ? s2t_opc64[63:32] : s2t_opc32) &
                                {32{grant_wb_to_fpxx_arith_i}};
      // for WB-result #2
      wb_fpxx_arith_res_lo_o <= s2t_opc64[31:0] &
                                {32{grant_wb_to_fpxx_arith_i & s1o_op_fp64_arith}};
    end
  end // @clock

  // WB: exception
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      wb_fpxx_arith_fpcsr_o  <= {`OR1K_FPCSR_ALLF_SIZE{1'b0}};
      wb_except_fpxx_arith_o <= 1'b0;
    end
    else if(pipeline_flush_i) begin
      wb_fpxx_arith_fpcsr_o  <= {`OR1K_FPCSR_ALLF_SIZE{1'b0}};
      wb_except_fpxx_arith_o <= 1'b0;
    end
    else if(padv_wb_i) begin
      wb_fpxx_arith_fpcsr_o  <= exec_fpxx_arith_fpcsr;
      wb_except_fpxx_arith_o <= exec_except_fpxx_arith_o;
    end
  end // @clock

  // WB: update FPCSR (1-clock to prevent extra writes into FPCSR)
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_fpxx_arith_wb_fpcsr_o <= 1'b0;
    else if (pipeline_flush_i)
      wb_fpxx_arith_wb_fpcsr_o <= 1'b0;
    else if (padv_wb_i)
      wb_fpxx_arith_wb_fpcsr_o <= grant_wb_to_fpxx_arith_i;
    else
      wb_fpxx_arith_wb_fpcsr_o <= 1'b0;
  end // @clock

endmodule // pfpu_rnd_marocchino
