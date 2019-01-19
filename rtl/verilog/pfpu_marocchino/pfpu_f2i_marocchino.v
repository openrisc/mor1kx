/////////////////////////////////////////////////////////////////////
//                                                                 //
//    pfpu_f2i_marocchino                                          //
//    32/64-bit floating point to 32/64 integer converter          //
//    for MAROCCHINO pipeline                                      //
//                                                                 //
//    Author: Andrey Bacherov                                      //
//            avbacherov@opencores.org                             //
//                                                                 //
/////////////////////////////////////////////////////////////////////
//                                                                 //
//   Copyright (C) 2014 - 2016 Andrey Bacherov                     //
//                             avbacherov@opencores.org            //
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

module pfpu_f2i_marocchino
(
  // clocks and resets
  input             cpu_clk,
  // pipe controls
  input             pipeline_flush_i,
  input             start_i,
  output            f2i_taking_op_o,
  output reg        f2i_rdy_o,
  input             rnd_taking_f2i_i,
  // input data
  input             signa_i,
  input      [12:0] exp13a_i,
  input      [52:0] fract53a_i,
  input             exec_op_fp64_arith_i,
  input             snan_i,
  input             qnan_i,
  // output data for rounding
  output reg        f2i_sign_o,
  output reg [52:0] f2i_int53_o,
  output reg  [5:0] f2i_shr_o,
  output reg  [3:0] f2i_shl_o,
  output reg        f2i_ovf_o
);

  /*
     Any stage's output is registered.
     Definitions:
       s??o_name - "S"tage number "??", "O"utput
       s??t_name - "S"tage number "??", "T"emporary (internally)
  */


  // F2I pipe controls
  //  ## per stage ready flags
  reg  s0o_ready, s0o_pending;
  //  ## per stage busy flags
  wire s1_busy = f2i_rdy_o & ~rnd_taking_f2i_i;
  wire s0_busy = s0o_ready & s0o_pending;
  //  ## per stage advance
  wire s0_adv  = start_i                   & ~s0_busy;
  wire s1_adv  = (s0o_ready | s0o_pending) & ~s1_busy;

  // F2I pipe takes operands for computation
  assign f2i_taking_op_o = s0_adv;


  /**** Stage #0: just latches for input data ****/

  reg         s0o_signa;
  reg  [12:0] s0o_exp13a;
  reg  [52:0] s0o_fract53a;
  reg         s0o_op_fp64_arith;
  reg         s0o_snan;
  reg         s0o_qnan;

  // ---
  always @(posedge cpu_clk) begin
    if (s0_adv) begin
      s0o_signa    <= signa_i;
      s0o_exp13a   <= exp13a_i;
      s0o_fract53a <= fract53a_i;
      s0o_op_fp64_arith <= exec_op_fp64_arith_i;
      s0o_snan     <= snan_i;
      s0o_qnan     <= qnan_i;
    end
  end // @cpu-clock

  // "stage #0 is ready" flag
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      s0o_ready <= 1'b0;
    else if (s0_adv)
      s0o_ready <= 1'b1;
    else if (s1_adv)
      s0o_ready <= s0_busy;
    else if (~s0o_pending)
      s0o_ready <= 1'b0;
  end // @cpu-clock

  // "there are pending data " flag
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      s0o_pending <= 1'b0;
    else if (s1_adv)
      s0o_pending <= 1'b0;
    else if (~s0o_pending)
      s0o_pending <= s0o_ready;
  end // @cpu-clock


  /**** Stage #1: computation and output latches ****/

  // exponent after moving binary point at the end of mantissa
  // bias is also removed:
  //  for double precision: (-1023 - 52) = -1075 = +13'h1bcd
  //  for single precision: ( -127 - 23) =  -150 = +13'h1f6a
  wire [12:0] s1t_exp13m = s0o_exp13a + (s0o_op_fp64_arith ? 13'h1bcd : 13'h1f6a);

  // detect if now shift right is required
  wire [12:0] s1t_shr_t = {13{s1t_exp13m[12]}} &
                          ((s0o_op_fp64_arith ? 13'd1075 : 13'd150) - s0o_exp13a);
  // limit right shift by 64
  wire  [5:0] s1t_shr = s1t_shr_t[5:0] | {6{|s1t_shr_t[12:6]}};

  // detect if left shift required for mantissa
  // (limited by 15)
  wire [3:0] s1t_shl = {4{~s1t_exp13m[12]}} & (s1t_exp13m[3:0] | {4{|s1t_exp13m[12:4]}});
  // check overflow
  //  overflow threshold (11 or 8) is (integer_length (64/32) minus full_mantissa_length (53/24))
  //  i.e. it is number of possible positions for left shift till integer overflow
  wire s1t_is_shl_gt11 = (s1t_shl  > (s0o_op_fp64_arith ? 4'd11 : 4'd8));
  wire s1t_is_shl_eq11 = (s1t_shl == (s0o_op_fp64_arith ? 4'd11 : 4'd8));
  wire s1t_is_shl_ovf =
     s1t_is_shl_gt11 |
    (s1t_is_shl_eq11 & (~s0o_signa)) |
    (s1t_is_shl_eq11 &   s0o_signa & (|s0o_fract53a[51:0]));


  // pending data latches
  reg         f2i_sign_p;
  wire        f2i_sign_w;
  reg  [52:0] f2i_int53_p;
  wire [52:0] f2i_int53_m;
  reg   [5:0] f2i_shr_p;
  reg   [3:0] f2i_shl_p;
  reg         f2i_ovf_p;

  // pre-out multiplexsors
  // for rounding engine we re-pack single precision 24-bits mantissa to LSBs
  assign f2i_sign_w  = s0o_signa & (~(s0o_qnan | s0o_snan)); // if 'a' is a NaN than ouput is max. positive
  assign f2i_int53_m = s0o_op_fp64_arith ? (s0o_fract53a) : ({29'd0,s0o_fract53a[52:29]});

  // pending data latches
  always @(posedge cpu_clk) begin
    if (~s0o_pending) begin
      f2i_sign_p  <= f2i_sign_w;
      f2i_int53_p <= f2i_int53_m;
      f2i_shr_p   <= s1t_shr;
      f2i_shl_p   <= s1t_shl;
      f2i_ovf_p   <= s1t_is_shl_ovf;
    end // advance
  end // @clock

  // registering output
  always @(posedge cpu_clk) begin
    if (s1_adv) begin
      f2i_sign_o  <= s0o_pending ? f2i_sign_p  : f2i_sign_w;
      f2i_int53_o <= s0o_pending ? f2i_int53_p : f2i_int53_m;
      f2i_shr_o   <= s0o_pending ? f2i_shr_p   : s1t_shr;
      f2i_shl_o   <= s0o_pending ? f2i_shl_p   : s1t_shl;
      f2i_ovf_o   <= s0o_pending ? f2i_ovf_p   : s1t_is_shl_ovf;
    end // advance
  end // @clock

  // ready is special case
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      f2i_rdy_o <= 1'b0;
    else if (s1_adv)
      f2i_rdy_o <= 1'b1;
    else if (rnd_taking_f2i_i)
      f2i_rdy_o <= 1'b0;
  end // @clock

endmodule // pfpu_f2i_marocchino
