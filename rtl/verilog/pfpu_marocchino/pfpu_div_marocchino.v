//////////////////////////////////////////////////////////////////////
//                                                                  //
//    pfpu_div_marocchino                                           //
//                                                                  //
//    This file is part of the mor1kx project                       //
//    https://github.com/openrisc/mor1kx                            //
//                                                                  //
//    Description                                                   //
//    divider pipeline for single and double precision              //
//    floating point numbers for MAROCCHINO pipeline                //
//                                                                  //
//    Author(s):                                                    //
//          Andrey Bacherov, avbacherov@opencores.org               //
//                                                                  //
//////////////////////////////////////////////////////////////////////
//                                                                  //
//  Copyright (C) 2015 - 2016                                       //
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


//----------------------------------------------------------------------------//
// SRT-4 kernel for 58-bits fractionals                                       //
// Opposite to integer version it also:                                       //
//  a) outputs reminder for correct sticky bit computation                    //
//  b) doesn't need signum of quotient                                        //
//  c) updated for double and single precision fractionals                    //
//     !!! DON'T CHANGE MODULE PARAMETERS !!!                                 //
//----------------------------------------------------------------------------//

module srt4_fract58
#(
    parameter N      = 58, // must be even
    parameter LOG2N2 =  5  // ceil(log2(N/2)): size of iteration counter
)
(
  // clock and reset
  input              clk,
  input              rst,
  // pipeline controls
  input              pipeline_flush_i,
  input              div_start_i,      // take operands and start
  output reg         div_proc_o,       // iterator busy
  output reg         div_valid_o,      // result ready
  input              wb_taking_div_i,  // Write Back is taking result
  // force zero result
  input              s1o_opc_0_i, // SRT4(fractionals)
  input              s1o_dbz_i, // SRT4(fractionals)
  // numerator and denominator
  input      [N-1:0] num_i,
  input      [N-1:0] den_i,
  // double / sigle precision mode selector
  input              s1o_op_fp64_arith_i,
  // outputs
  output reg         dbz_o,
  output     [N-1:0] rem_o,
  output     [N-1:0] qtnt_o
);

  // Reminder
  wire   [N:0] four_rem;   // 4*rem
  wire   [N:0] nrem;       // next reminder (4*rem - q_digit*den)
  reg    [N:0] prem_hi_r;  // partial reminder: initially = {0,num(2n-1)...num(n)}
  wire   [3:0] trunc_rem;  // truncated partial reminder

  // force results to zero and skip iterations
  wire zer = s1o_dbz_i | s1o_opc_0_i; // in SRT4(fractionals)


  // Each iteration starts from qoutient digit selection
  assign trunc_rem = prem_hi_r[N:N-3];
  // quotient's special digits
  reg [2:0] q_digit_2or3_r;
  reg [2:0] q_digit_minus_2or3_r;
  // ---
  always @(posedge clk) begin
    if (div_start_i) begin
      q_digit_2or3_r       <= {2'b01, ~den_i[N-2]};
      q_digit_minus_2or3_r <= { 1'b1,  den_i[N-2], ~den_i[N-2]};
    end
  end
  // signed digit selection
  reg [2:0] q_digit; // [2] - signum
  // ---
  always @(*) begin
    // synthesis parallel_case full_case
    casez (trunc_rem)
      4'b0000: q_digit = 3'b000;
      4'b0001: q_digit = 3'b001;
      4'b0010: q_digit = 3'b010;
      4'b0011: q_digit = q_digit_2or3_r;
      4'b01??: q_digit = 3'b011; // 0100 ... 0111
      4'b10??: q_digit = 3'b101; // 1000 ... 1011
      4'b1100: q_digit = q_digit_minus_2or3_r;
      4'b1101: q_digit = 3'b110;
      4'b1110: q_digit = 3'b111;
      default: q_digit = 3'b000;
    endcase
  end

  // Prepare multiple versions of denominator
  reg [N-1:0] one_den_r;    // 1 * denominator
  reg   [N:0] three_den_r;  // 3 * denominator
  // ---
  always @(posedge clk) begin
    if (div_start_i) begin
      one_den_r   <= den_i;
      three_den_r <= {1'b0, den_i} + {den_i, 1'b0};
    end
  end
  // select the multiple denominator
  reg [N:0] mult_den; // : 0 / den / 2*den / 3*den
  // second operand selection
  always @(*) begin
    // synthesis parallel_case full_case
    case (q_digit)
      3'b000:  mult_den = {(N+1){1'b0}};     // 0 * denominator
      3'b001:  mult_den = {1'b0, one_den_r}; // 1 * denominator
      3'b010:  mult_den = {one_den_r, 1'b0}; // 2 * denominator
      3'b011:  mult_den = three_den_r;       // 3 * denominator
      3'b101:  mult_den = three_den_r;       // 3 * denominator
      3'b110:  mult_den = {one_den_r, 1'b0}; // 2 * denominator
      default: mult_den = {1'b0, one_den_r}; // 1 * denominator
    endcase
  end

  assign four_rem  = {prem_hi_r[N-2:0],2'd0};
  // next reminder
  wire   sub  = ~q_digit[2]; // substract
  // sub ? (4*REM - MultDen) : (4*REM + MultDen)
  assign nrem = four_rem + (mult_den ^ {(N+1){sub}}) + {{N{1'b0}},sub};

  // and partial reminder update
  always @(posedge clk) begin
    if (div_start_i)
      prem_hi_r <= {1'b0,({N{~zer}} & num_i)};
    else if (div_proc_o)
      prem_hi_r <= nrem;
  end // @clock

  // signed digits to tow's complement on the fly convertor
  //  # part Q
  reg   [N-1:0] q_r;
  //  # ---
  always @(posedge clk) begin
    if (div_start_i)
      q_r <= {N{1'b0}};
    else if (div_proc_o) begin
      // synthesis parallel_case full_case
      case (q_digit)
        3'b000:  q_r <= { q_r[N-3:0],2'b00};
        3'b001:  q_r <= { q_r[N-3:0],2'b01};
        3'b010:  q_r <= { q_r[N-3:0],2'b10};
        3'b011:  q_r <= { q_r[N-3:0],2'b11};
        3'b101:  q_r <= {qm_r[N-3:0],2'b01};
        3'b110:  q_r <= {qm_r[N-3:0],2'b10};
        default: q_r <= {qm_r[N-3:0],2'b11};
      endcase
    end
  end // @clock
  //  # part QM
  reg   [N-1:0] qm_r;
  //  # ---
  always @(posedge clk) begin
    if (div_start_i)
      qm_r <= {{(N-2){1'b0}},2'b11};
    else if (div_proc_o) begin
      // synthesis parallel_case full_case
      case (q_digit)
        3'b000:  qm_r <= {qm_r[N-3:0],2'b11};
        3'b001:  qm_r <= { q_r[N-3:0],2'b00};
        3'b010:  qm_r <= { q_r[N-3:0],2'b01};
        3'b011:  qm_r <= { q_r[N-3:0],2'b10};
        3'b101:  qm_r <= {qm_r[N-3:0],2'b00};
        3'b110:  qm_r <= {qm_r[N-3:0],2'b01};
        default: qm_r <= {qm_r[N-3:0],2'b10};
      endcase
    end
  end // @clock

  // Outputs
  //  # if REM < 0 than { REM += D; Q -= 1; }
  //  # reminder
  assign rem_o  = prem_hi_r[N-1:0] + ({N{prem_hi_r[N]}} & one_den_r[N-1:0]);
  //  # quotient
  // ---
  assign qtnt_o = q_r + {N{prem_hi_r[N]}};


  // iterations controller
  // ---
  localparam [LOG2N2-1:0] DIV_COUNT_MAX_D = 5'd28; // double precision: (58/2) - 1
  localparam [LOG2N2-1:0] DIV_COUNT_MAX_S = 5'd13; // single precision: (28/2) - 1
  // ---
  reg [LOG2N2-1:0] div_count_r;
  // division controller
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      div_valid_o <= 1'b0;
      dbz_o       <= 1'b0;
      div_proc_o  <= 1'b0;
      div_count_r <= {LOG2N2{1'b0}};
    end
    if (pipeline_flush_i) begin
      div_valid_o <= 1'b0;
      dbz_o       <= 1'b0;
      div_proc_o  <= 1'b0;
      div_count_r <= {LOG2N2{1'b0}};
    end
    else if (div_start_i) begin
      if (zer) begin
        div_valid_o <= 1'b1;
        dbz_o       <= s1o_dbz_i; // in SRT4(fractionals)
        div_proc_o  <= 1'b0;
        div_count_r <= {LOG2N2{1'b0}};
      end
      else begin
        div_valid_o <= 1'b0;
        dbz_o       <= 1'b0;
        div_proc_o  <= 1'b1;
        div_count_r <= s1o_op_fp64_arith_i ? DIV_COUNT_MAX_D : DIV_COUNT_MAX_S;
      end
    end
    else if (wb_taking_div_i) begin
      div_valid_o <= 1'b0;
      dbz_o       <= 1'b0;
      div_proc_o  <= 1'b0;
      div_count_r <= {LOG2N2{1'b0}};
    end
    else if (div_proc_o) begin
      if (~(|div_count_r)) begin // == 0
        div_valid_o <= 1'b1;
        div_proc_o  <= 1'b0;
      end
      else
        div_count_r <= div_count_r + {LOG2N2{1'b1}}; // -= 1
    end
  end // @clock

endmodule // srt4_fract58


//---------------//
// Division pipe //
//---------------//

module pfpu_div_marocchino
(
  // clocks and resets
  input             clk,
  input             rst,
  // pipe controls
  input             pipeline_flush_i,
  input             s1o_div_ready_i,
  output            div_busy_o,
  output            div_taking_op_o,
  output reg        div_rdy_o,         // result ready
  input             rnd_taking_div_i,
  // operands
  input             s1o_signc_i,
  input      [12:0] s1o_exp13c_i,
  input       [5:0] s2t_shrx_i,
  input      [12:0] s2t_exp13rx_i,
  input      [52:0] s1o_fract53a_i,
  input      [52:0] s1o_fract53b_i,
  input             s1o_opc_0_i,
  input             s1o_dbz_i,
  input             s1o_op_fp64_arith_i,
  // MUL outputs
  output reg        div_sign_o,      // signum
  output reg  [5:0] div_shr_o,       // do right shift in align stage
  output reg [12:0] div_exp13shr_o,  // exponent for right shift align
  output reg        div_shl_o,       // do left shift in align stage
  output reg [12:0] div_exp13shl_o,  // exponent for left align
  output reg [12:0] div_exp13sh0_o,  // exponent for no shift in align
  output reg [56:0] div_fract57_o,   // fractional with appended {r,s} bits
  output reg        div_dbz_o        // divisin by zero
);

  /*
     Any stage's output is registered.
     Definitions:
       s??o_name - "S"tage number "??", "O"utput
       s??t_name - "S"tage number "??", "T"emporary (internally)
  */

  // divider pipeline controls
  //  ## ready signals per stage
  wire  s2o_div_ready, s2o_proc;
  //  ## busy per stage
  wire out_busy = div_rdy_o & ~rnd_taking_div_i;
  wire s2_busy  = s2o_proc | (s2o_div_ready & out_busy);
  //  ## advance per stage
  wire s2_adv  = s1o_div_ready_i & ~s2_busy;
  wire out_adv = s2o_div_ready   & ~out_busy;
  //  ## multiplier is taking operands
  assign div_busy_o      = s1o_div_ready_i & s2_busy;
  assign div_taking_op_o = s2_adv;


  // stage #2 outputs
  reg        s2o_opc_0;
  reg        s2o_signc;
  reg [12:0] s2o_exp13c;
  reg  [5:0] s2o_shrx;
  reg [12:0] s2o_exp13rx;
  //   division by zero flag
  wire       s2o_dbz;
  //   double / single mode selector
  reg        s2o_op_fp64_arith;
  //   registering
  always @(posedge clk) begin
    if (s2_adv) begin
      s2o_opc_0         <= s1o_opc_0_i;
      s2o_signc         <= s1o_signc_i;
      s2o_exp13c        <= s1o_exp13c_i;
      s2o_shrx          <= s2t_shrx_i;
      s2o_exp13rx       <= s2t_exp13rx_i;
      s2o_op_fp64_arith <= s1o_op_fp64_arith_i;
    end // advance pipe
  end // posedge clock

  wire [57:0] s3t_rem58;
  wire [57:0] s3t_qtnt58;

  // we use right shifted numenator to guarantee
  // (numenator < denominator) condition
  srt4_fract58 u_srt4_fract
  (
    // clock and reset
    .clk                  (clk), // SRT4-FRACT
    .rst                  (rst), // SRT4-FRACT
    // pipeline controls
    .pipeline_flush_i     (pipeline_flush_i), // SRT4-FRACT
    .div_start_i          (s2_adv), // SRT4-FRACT
    .div_proc_o           (s2o_proc), // SRT4-FRACT
    .div_valid_o          (s2o_div_ready), // SRT4-FRACT
    .wb_taking_div_i      (out_adv),
    // force zero result
    .s1o_opc_0_i          (s1o_opc_0_i), // SRT4-FRACT
    .s1o_dbz_i            (s1o_dbz_i), // SRT4-FRACT
    // numerator and denominator
    .num_i                ({2'b0,s1o_fract53a_i,3'd0}), // SRT4-FRACT
    .den_i                ({s1o_fract53b_i,5'd0}), // SRT4-FRACT
    // double / sigle precision mode selector
    .s1o_op_fp64_arith_i  (s1o_op_fp64_arith_i), // SRT4-FRACT
    // outputs
    .dbz_o                (s2o_dbz), // SRT4-FRACT
    .rem_o                (s3t_rem58), // SRT4-FRACT
    .qtnt_o               (s3t_qtnt58) // SRT4-FRACT
  );


  /* Stage #3: formatting and latching output */


  // Quotient for rounding stage
  //  double precision 57 bits: 0?.ff-52-ff[r/f][s/r][s2/s2]
  //                                                 ^^^^^^^ [1:0] bits of QTNT-58
  //  single precision 28 bits: 0?.ff-23-ff[r/f][s/r][s2/s2]
  //                                                 ^^^^^^^ [0] bit of QTNT-58
  //                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ packed in LSB for rounding
  wire        s3t_sticky = (s2o_op_fp64_arith & s3t_qtnt58[1]) | (s3t_qtnt58[0]) | (|s3t_rem58);
  wire [56:0] s3t_qtnt57 = {(s2o_op_fp64_arith ? (s3t_qtnt58[57:2]) : (s3t_qtnt58[56:1])), s3t_sticky};

  // Possible left shift computation.
  // In fact, as the dividend and divisor was normalized
  //   and the result is non-zero
  //   the '1' is maximum number of leading zeros in the quotient.
  wire s3t_nlz = s2o_op_fp64_arith ? (~s3t_qtnt58[56]) : (~s3t_qtnt58[26]);
  wire [12:0] s3t_exp13_m1 = s2o_exp13c - 13'd1;
  // left shift flag and corrected exponent
  wire        s3t_shlx;
  wire [12:0] s3t_exp13lx;
  assign {s3t_shlx,s3t_exp13lx} =
      // shift isn't needed (includes zero result)
    (~s3t_nlz)            ? {1'b0,s2o_exp13c} :
      // normalization is possible
    (s2o_exp13c >  13'd1) ? {1'b1,s3t_exp13_m1} :
      // denormalized and zero cases
                            {1'b0,{12'd0,~s2o_opc_0}};

  // output
  always @(posedge clk) begin
    if (out_adv) begin
      div_sign_o     <= s2o_signc;
      div_shr_o      <= s2o_shrx;
      div_exp13shr_o <= s2o_exp13rx;
      div_shl_o      <= s3t_shlx;
      div_exp13shl_o <= s3t_exp13lx;
      div_exp13sh0_o <= s2o_exp13c;
      div_fract57_o  <= s3t_qtnt57;
    end // advance pipe
  end // posedge clock
  // division by zero flag
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      div_dbz_o <= 1'b0;
    else if (out_adv)
      div_dbz_o <= s2o_dbz;
  end // posedge clock


  // ready is special case
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      div_rdy_o <= 1'b0;
    else if (pipeline_flush_i)
      div_rdy_o <= 1'b0;
    else if (out_adv)
      div_rdy_o <= 1'b1;
    else if (rnd_taking_div_i)
      div_rdy_o <= 1'b0;
  end // posedge clock

endmodule // pfpu_div_marocchino


