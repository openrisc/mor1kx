//////////////////////////////////////////////////////////////////////
//                                                                  //
//    pfpu_mul_marocchino                                           //
//                                                                  //
//    This file is part of the mor1kx project                       //
//    https://github.com/openrisc/mor1kx                            //
//                                                                  //
//    Description                                                   //
//    multiplier pipeline for single and double precision           //
//    floating point numbers for MAROCCHINO pipeline                //
//                                                                  //
//    Author(s):                                                    //
//          Andrey Bacherov, avbacherov@opencores.org               //
//                                                                  //
//////////////////////////////////////////////////////////////////////
//                                                                  //
//  Copyright (C) 2015 - 2017                                       //
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

module pfpu_mul_marocchino
(
  // clocks and resets
  input             cpu_clk,
  // pipe controls
  input             pipeline_flush_i,
  input             s1o_mul_ready_i,
  output            mul_busy_o,
  output            mul_taking_op_o,
  output reg        mul_rdy_o,         // result ready
  input             rnd_taking_mul_i,
  // operands
  input             s1o_signc_i,
  input      [12:0] s1o_exp13c_i,
  input       [5:0] s2t_shrx_i,
  input      [12:0] s2t_exp13rx_i,
  input      [52:0] s1o_fract53a_i,
  input      [52:0] s1o_fract53b_i,
  input             s1o_op_fp64_arith_i,
  // MUL outputs
  output reg        mul_sign_o,      // signum
  output reg  [5:0] mul_shr_o,       // do right shift in align stage
  output reg [12:0] mul_exp13shr_o,  // exponent for right shift align
  output reg [12:0] mul_exp13sh0_o,  // exponent for no shift in align
  output reg [56:0] mul_fract57_o    // fractional with appended {r,s} bits
);

  /*
     Any stage's output is registered.
     Definitions:
       s??o_name - "S"tage number "??", "O"utput
       s??t_name - "S"tage number "??", "T"emporary (internally)
  */

  // multiplier pipeline controls
  //  ## ready signals per stage
  reg  s2o_mul_ready, s3o_mul_ready,
       s4o_mul_ready, s5o_mul_ready,
       s6o_mul_ready;
  reg  s2o_op_fp64_arith, s3o_op_fp64_arith, s4o_op_fp64_arith;
  //  ## busy per stage
  wire out_busy = mul_rdy_o & ~rnd_taking_mul_i;
  wire s6_busy  = s6o_mul_ready & out_busy;
  wire s5_busy  = s5o_mul_ready & s6_busy;
  wire s4_busy  = s4o_mul_ready & ((s5_busy & s4o_op_fp64_arith) |
                                   ((out_busy | s6o_mul_ready | s5o_mul_ready) & ~s4o_op_fp64_arith));
  wire s3_busy  = s3o_mul_ready & s4_busy;
  wire s2_busy  = s2o_mul_ready & s3_busy;
  //  ## advance per stage
  wire s2_adv    = s1o_mul_ready_i & ~s2_busy;
  wire s3_adv    = s2o_mul_ready   & ~s3_busy;
  wire s4_adv    = s3o_mul_ready   & ~s4_busy;
  wire s5_adv    = s4o_mul_ready   & ~s5_busy & s4o_op_fp64_arith;
  wire s6_adv    = s5o_mul_ready   & ~s6_busy;
  wire out_adv_d = s6o_mul_ready   & ~out_busy; // for double precision
  wire out_adv_s = s4o_mul_ready   & ~out_busy & ~s6o_mul_ready & ~s5o_mul_ready & ~s4o_op_fp64_arith;
  //  ## multiplier is taking operands
  assign mul_busy_o      = s1o_mul_ready_i & s2_busy;
  assign mul_taking_op_o = s2_adv;


  /* Stage #2 */


  // split operands on 4 part
  //  ## operand A
  wire [12:0] s2t_a0 = s1o_fract53a_i[12: 0];
  wire [12:0] s2t_a1 = s1o_fract53a_i[25:13];
  wire [12:0] s2t_a2 = s1o_fract53a_i[38:26];
  wire [13:0] s2t_a3 = s1o_fract53a_i[52:39];
  //  ## operand B
  wire [12:0] s2t_b0 = s1o_fract53b_i[12: 0];
  wire [12:0] s2t_b1 = s1o_fract53b_i[25:13];
  wire [12:0] s2t_b2 = s1o_fract53b_i[38:26];
  wire [13:0] s2t_b3 = s1o_fract53b_i[52:39];


  // stage #2 outputs
  //   computation related
  reg        s2o_signc;
  reg [12:0] s2o_exp13c;
  reg  [5:0] s2o_shrx;
  reg [12:0] s2o_exp13rx;
  //   all 16 partial multiplies
  reg [25:0] s2o_a0b0, s2o_a0b1, s2o_a1b0, s2o_a1b1;
  reg [25:0] s2o_a0b2, s2o_a2b0;
  reg [26:0] s2o_a0b3, s2o_a3b0;
  reg [25:0] s2o_a1b2, s2o_a2b1;
  reg [26:0] s2o_a1b3, s2o_a3b1;
  reg [25:0] s2o_a2b2;
  reg [26:0] s2o_a2b3, s2o_a3b2;
  reg [27:0] s2o_a3b3;
  //   registering
  always @(posedge cpu_clk) begin
    if (s2_adv) begin
      // computation related
      s2o_signc         <= s1o_signc_i;
      s2o_exp13c        <= s1o_exp13c_i;
      s2o_shrx          <= s2t_shrx_i;
      s2o_exp13rx       <= s2t_exp13rx_i;
      s2o_op_fp64_arith <= s1o_op_fp64_arith_i;
      // partial multiplies
      s2o_a0b0 <= s2t_a0 * s2t_b0;
      s2o_a0b1 <= s2t_a0 * s2t_b1;
      s2o_a1b0 <= s2t_a1 * s2t_b0;
      s2o_a1b1 <= s2t_a1 * s2t_b1;
      s2o_a0b2 <= s2t_a0 * s2t_b2;
      s2o_a2b0 <= s2t_a2 * s2t_b0;
      s2o_a0b3 <= {1'b0,s2t_a0} * s2t_b3;
      s2o_a3b0 <= s2t_a3 * {1'b0,s2t_b0};
      s2o_a1b2 <= s2t_a1 * s2t_b2;
      s2o_a2b1 <= s2t_a2 * s2t_b1;
      s2o_a1b3 <= {1'b0,s2t_a1} * s2t_b3;
      s2o_a3b1 <= s2t_a3 * {1'b0,s2t_b1};
      s2o_a2b2 <= s2t_a2 * s2t_b2;
      s2o_a2b3 <= {1'b0,s2t_a2} * s2t_b3;
      s2o_a3b2 <= s2t_a3 * {1'b0,s2t_b2};
      s2o_a3b3 <= s2t_a3 * s2t_b3;
    end // advance pipe
  end // @clock

  // ready is special case
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      s2o_mul_ready <= 1'b0;
    else if (s2_adv)
      s2o_mul_ready <= 1'b1;
    else if (s3_adv)
      s2o_mul_ready <= 1'b0;
  end // @clock


  /* Stage #3 */


  // stage #3 outputs
  //   computation related
  reg        s3o_signc;
  reg [12:0] s3o_exp13c;
  reg  [5:0] s3o_shrx;
  reg [12:0] s3o_exp13rx;
  //   partial sum and sticky
  reg        s3o_sticky;
  reg [26:0] s3o_sum27_a1b0;
  reg [38:0] s3o_cat39_a1b1;
  reg [26:0] s3o_sum27_a2b0;
  reg [27:0] s3o_sum28_a3b0;
  reg [26:0] s3o_sum27_a2b1;
  reg [27:0] s3o_sum28_a3b1;
  reg [27:0] s3o_sum28_a3b2;
  reg [53:0] s3o_cat54_a3b3;
  //   registering
  always @(posedge cpu_clk) begin
    if (s3_adv) begin
      // computation related
      s3o_signc         <= s2o_signc;
      s3o_exp13c        <= s2o_exp13c;
      s3o_shrx          <= s2o_shrx;
      s3o_exp13rx       <= s2o_exp13rx;
      s3o_op_fp64_arith <= s2o_op_fp64_arith;
      // partial sum and sticky
      s3o_sticky     <= |s2o_a0b0[12:0];
      s3o_sum27_a1b0 <= s2o_a1b0 + s2o_a0b1;
      s3o_cat39_a1b1 <= {s2o_a1b1,s2o_a0b0[25:13]};
      s3o_sum27_a2b0 <= s2o_a2b0 + s2o_a0b2;
      s3o_sum28_a3b0 <= s2o_a3b0 + s2o_a0b3;
      s3o_sum27_a2b1 <= s2o_a2b1 + s2o_a1b2;
      s3o_sum28_a3b1 <= s2o_a3b1 + s2o_a1b3;
      s3o_sum28_a3b2 <= s2o_a3b2 + s2o_a2b3;
      s3o_cat54_a3b3 <= {s2o_a3b3,s2o_a2b2};
    end // advance pipe
  end // @clock

  // ready is special case
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      s3o_mul_ready <= 1'b0;
    else if (s3_adv)
      s3o_mul_ready <= 1'b1;
    else if (s4_adv)
      s3o_mul_ready <= 1'b0;
  end // @clock


  /* Stage #4 */


  // stage #4 outputs
  //   computation related
  reg        s4o_signc;
  reg [12:0] s4o_exp13c;
  reg  [5:0] s4o_shrx;
  reg [12:0] s4o_exp13rx;
  //   partial sums and sticky
  reg        s4o_sticky;
  reg [38:0] s4o_sum39_a1b1;
  reg [40:0] s4o_sum41_a3b0;
  reg [40:0] s4o_sum41_a3b1;
  reg [53:0] s4o_sum54_a3b3;
  //   registering
  always @(posedge cpu_clk) begin
    if (s4_adv) begin
      // computation related
      s4o_signc         <= s3o_signc;
      s4o_exp13c        <= s3o_exp13c;
      s4o_shrx          <= s3o_shrx;
      s4o_exp13rx       <= s3o_exp13rx;
      s4o_op_fp64_arith <= s3o_op_fp64_arith;
      // partial sums and sticky
      s4o_sticky     <= s3o_sticky;
      s4o_sum39_a1b1 <= s3o_cat39_a1b1 + {12'd0,s3o_sum27_a1b0};
      s4o_sum41_a3b0 <= {(s3o_sum28_a3b0 + {14'd0,s3o_sum27_a2b0[26:13]}), s3o_sum27_a2b0[12:0]};
      s4o_sum41_a3b1 <= {(s3o_sum28_a3b1 + {14'd0,s3o_sum27_a2b1[26:13]}), s3o_sum27_a2b1[12:0]};
      s4o_sum54_a3b3 <= {(s3o_cat54_a3b3[53:13] + {13'd0,s3o_sum28_a3b2}), s3o_cat54_a3b3[12:0]};
    end // advance pipe
  end // @clock

  // ready is special case
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      s4o_mul_ready <= 1'b0;
    else if (s4_adv)
      s4o_mul_ready <= 1'b1;
    else if (s5_adv | out_adv_s)
      s4o_mul_ready <= 1'b0;
  end // @clock


  /* Stage #5 */


  // fractional for single precision: hh.ff-23-ff
  // and [q][r][s] bits
  wire [24:0] s5t_f32_fract25 = s4o_sum39_a1b1[34:10];
  wire  [2:0] s5t_f32_qrs = {s4o_sum39_a1b1[9:8], // f32: {q,r}
                             ((|s4o_sum39_a1b1[7:0]) | s4o_sticky)}; // f32: {s}

  wire        s5t_shrx_n0 = (|s4o_shrx);
  wire  [5:0] s5t_shrx    = s5t_shrx_n0 ? s4o_shrx : {5'd0,s5t_f32_fract25[24]};
  wire [12:0] s5t_exp13rx = s5t_shrx_n0 ? s4o_exp13rx : (s4o_exp13c + {12'd0,s5t_f32_fract25[24]});

  // stage #5 outputs
  //   computation related
  reg        s5o_signc;
  reg [12:0] s5o_exp13c;
  reg  [5:0] s5o_shrx;
  reg [12:0] s5o_exp13rx;
  //   partial sums and sticky
  reg        s5o_sticky;
  reg [40:0] s5o_sum41_a3b0;
  reg [66:0] s5o_sum67_a3b3;
  //   registering
  always @(posedge cpu_clk) begin
    if (s5_adv) begin
      // computation related
      s5o_signc   <= s4o_signc;
      s5o_exp13c  <= s4o_exp13c;
      s5o_shrx    <= s4o_shrx;
      s5o_exp13rx <= s4o_exp13rx;
      // partial sums and sticky
      s5o_sticky     <= (|s4o_sum39_a1b1[12:0]) | s4o_sticky;
      s5o_sum41_a3b0 <= s4o_sum41_a3b0 + {15'd0,s4o_sum39_a1b1[38:13]};
      s5o_sum67_a3b3 <= {(s4o_sum54_a3b3 + {26'd0,s4o_sum41_a3b1[40:13]}),s4o_sum41_a3b1[12:0]};
    end // advance pipe
  end // @clock

  // ready is special case
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      s5o_mul_ready <= 1'b0;
    else if (s5_adv)
      s5o_mul_ready <= 1'b1;
    else if (s6_adv)
      s5o_mul_ready <= 1'b0;
  end // @clock


  /* Stage #6: */


  // stage #6 outputs
  //   computation related
  reg        s6o_signc;
  reg [12:0] s6o_exp13c;
  reg  [5:0] s6o_shrx;
  reg [12:0] s6o_exp13rx;
  //   partial sums and sticky
  reg        s6o_sticky;
  reg [66:0] s6o_sum67;
  //   registering
  always @(posedge cpu_clk) begin
    if (s6_adv) begin
      // computation related
      s6o_signc   <= s5o_signc;
      s6o_exp13c  <= s5o_exp13c;
      s6o_shrx    <= s5o_shrx;
      s6o_exp13rx <= s5o_exp13rx;
      // partial sums and sticky
      s6o_sticky <= (|s5o_sum41_a3b0[12:0]) | s5o_sticky;
      s6o_sum67  <= s5o_sum67_a3b3 + {39'd0,s5o_sum41_a3b0[40:13]};
    end // advance pipe
  end // @clock

  // ready is special case
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      s6o_mul_ready <= 1'b0;
    else if (s6_adv)
      s6o_mul_ready <= 1'b1;
    else if (out_adv_d)
      s6o_mul_ready <= 1'b0;
  end // @clock


  /* Output */

  wire [53:0] s7t_f64_fract54 = s6o_sum67[66:13];
  wire  [2:0] s7t_f64_qrs     = {s6o_sum67[12:11],
                                 ((|s6o_sum67[10:0]) | s6o_sticky)};

  wire        s7t_shrx_n0 = (|s6o_shrx);
  wire  [5:0] s7t_shrx    = s7t_shrx_n0 ? s6o_shrx : {5'd0,s6o_sum67[66]};
  wire [12:0] s7t_exp13rx = s7t_shrx_n0 ? s6o_exp13rx : (s6o_exp13c + {12'd0,s6o_sum67[66]});

  always @(posedge cpu_clk) begin
    if (out_adv_d | out_adv_s) begin
      mul_sign_o     <= (s6o_mul_ready ? s6o_signc   : s4o_signc);
      mul_shr_o      <= (s6o_mul_ready ? s7t_shrx    : s5t_shrx);
      mul_exp13shr_o <= (s6o_mul_ready ? s7t_exp13rx : s5t_exp13rx);
      mul_exp13sh0_o <= (s6o_mul_ready ? s6o_exp13c  : s4o_exp13c);
      mul_fract57_o  <= (s6o_mul_ready ? {s7t_f64_fract54,s7t_f64_qrs} : {29'd0,s5t_f32_fract25,s5t_f32_qrs});
    end // advance pipe
  end // @clock

  // ready is special case
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      mul_rdy_o <= 1'b0;
    else if (out_adv_d | out_adv_s)
      mul_rdy_o <= 1'b1;
    else if (rnd_taking_mul_i)
      mul_rdy_o <= 1'b0;
  end // @clock

endmodule // pfpu_mul_marocchino
