/////////////////////////////////////////////////////////////////////
////                                                             ////
////  pfpu32_f2i                                                 ////
////  32-bit floating point to integer converter                 ////
////                                                             ////
////  Author: Andrey Bacherov                                    ////
////          avbacherov@opencores.org                           ////
////                                                             ////
/////////////////////////////////////////////////////////////////////
////                                                             ////
//// Copyright (C) 2014 Andrey Bacherov                          ////
////                    avbacherov@opencores.org                 ////
////                                                             ////
//// This source file may be used and distributed without        ////
//// restriction provided that this copyright statement is not   ////
//// removed from the file and that any derivative work contains ////
//// the original copyright notice and the associated disclaimer.////
////                                                             ////
////     THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY     ////
//// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED   ////
//// TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS   ////
//// FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL THE AUTHOR      ////
//// OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,         ////
//// INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES    ////
//// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE   ////
//// GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR        ////
//// BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF  ////
//// LIABILITY, WHETHER IN  CONTRACT, STRICT LIABILITY, OR TORT  ////
//// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT  ////
//// OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE         ////
//// POSSIBILITY OF SUCH DAMAGE.                                 ////
////                                                             ////
/////////////////////////////////////////////////////////////////////

`include "mor1kx-defines.v"

module pfpu32_f2i
(
   input             clk,
   input             rst,
   input [1:0]       rmode_i,
   input [31:0]      opa_i,
   input             flush_i,  // flush pipe
   input             adv_i,    // advance pipe
   input             start_i,  // start conversion
   output reg [31:0] out_o,
   output reg        nan_o,
   output reg        ine_o,
   output reg        inv_o,
   output reg        unf_o,
   output reg        zer_o,
   output reg        ready_o
);
  /*
     Any stage's output is registered.
     Definitions:
       s??o_name - "S"tage number "??", "O"utput
       s??t_name - "S"tage number "??", "T"emporary (internally)
  */

  wire [7:0]  s1t_expa   = opa_i[30:23];
  wire [22:0] s1t_fracta = opa_i[22:0];
  //   collect operands related information
  wire s1t_signa   = opa_i[31];
  wire s1t_expa_ff = &s1t_expa;
  wire s1t_infa    = s1t_expa_ff & !(|s1t_fracta);
  wire s1t_qnan_a  = s1t_expa_ff & s1t_fracta[22];
  wire s1t_snan_a  = s1t_expa_ff & (!s1t_fracta[22] & (|s1t_fracta[21:0]));
  //   opa is denormalized
  wire s1t_opa_0 = !(|opa_i[30:0]);
  wire s1t_opa_dn = !(|s1t_expa) & !s1t_opa_0;
  //   restored exponent and 24-bit mantissa
  wire [7:0]  s1t_exp8a = s1t_expa + {7'd0,s1t_opa_dn};
  wire [23:0] s1t_fract24a = {(!s1t_opa_dn & !s1t_opa_0),s1t_fracta};
  
  // prepare for fraction align
  //  precomputed values
  wire [7:0] s1t_shv = s1t_exp8a - 8'd126;
  wire s1t_fracta_n0 = |s1t_fracta;
  // determine useful align values and preliminary overflow/round/sticky flags
  wire [5:0] s1t_shl;
  wire s1t_ovf; // overflow -> maximum positive or nefative limit is guaranteed
  wire s1t_shr_r,s1t_shr_s; // round, sticky for right shift
  assign {s1t_shl,s1t_ovf,s1t_shr_r,s1t_shr_s} =
    // |f| < 0.5 : prserve sticky
    (s1t_exp8a <  8'd126) ? {6'd0,1'b0,1'b0,|s1t_fract24a} :
    // 0.5 <= |f| < 1 : preserve round and sticky
    (s1t_exp8a == 8'd126) ? {6'd0,1'b0,s1t_fract24a[23],s1t_fracta_n0} :
    // possible shift left as for positive as for negative values
    (s1t_exp8a <  8'd158) ? {s1t_shv[5:0],1'b0,1'b0,1'b0} :
    // possible shift left specially for negative values
    ((s1t_exp8a == 8'd158) & s1t_signa) ? {(6'd32 & {6{!s1t_fracta_n0}}),s1t_fracta_n0,1'b0,1'b0} :
    // guaranteed overflow (align is useless)
                                          {6'd0,1'b1,1'b0,1'b0};


  // stage #1 outputs
  //   input related
  reg s1o_infa, s1o_qnan_a, s1o_snan_a;
  //   computation related
  reg        s1o_sign;
  reg [23:0] s1o_fract24;
  reg [5:0]  s1o_shl;
  reg [1:0]  s1o_shr_rs;
  reg        s1o_ovf;

  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s1o_infa    <= s1t_infa;
      s1o_qnan_a  <= s1t_qnan_a;
      s1o_snan_a  <= s1t_snan_a;
        // computation related
      s1o_sign    <= s1t_signa;
      s1o_fract24 <= s1t_fract24a;
      s1o_shl     <= s1t_shl;
      s1o_shr_rs  <= {s1t_shr_r,s1t_shr_s};
      s1o_ovf     <= s1t_ovf;
    end // (reset or flush) / advance
  end // posedge clock

  // ready is special case
  reg s1o_ready;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      s1o_ready <= 0;
    else if(flush_i)
      s1o_ready <= 0;
    else if(adv_i)
      s1o_ready <= start_i;
  end // posedge clock


  /* Stage #2: */

  // shifted integer
  wire [55:0] s2t_int55 = {32'd0,s1o_fract24} << s1o_shl;
  // extracted integer
  wire [31:0] s2t_int32 =
    (|s1o_shl) ? s2t_int55[55:24] : 32'd0;

  // round and sticky for shift left
  //   makes sense for non-zero shift only
  //   (otherwise either right shift round/sticky or overflow)
  reg [1:0] s2t_rs;
  always @(s1o_shl) begin
    case (s1o_shl)  // synopsys full_case parallel_case
      5'd0 : s2t_rs = s1o_shr_rs; // either right shift round/sticky or overflow
      5'd1 : s2t_rs = {s1o_fract24[22],|s1o_fract24[21:0]};
      5'd2 : s2t_rs = {s1o_fract24[21],|s1o_fract24[20:0]};
      5'd3 : s2t_rs = {s1o_fract24[20],|s1o_fract24[19:0]};
      5'd4 : s2t_rs = {s1o_fract24[19],|s1o_fract24[18:0]};
      5'd5 : s2t_rs = {s1o_fract24[18],|s1o_fract24[17:0]};
      5'd6 : s2t_rs = {s1o_fract24[17],|s1o_fract24[16:0]};
      5'd7 : s2t_rs = {s1o_fract24[16],|s1o_fract24[15:0]};
      5'd8 : s2t_rs = {s1o_fract24[15],|s1o_fract24[14:0]};
      5'd9 : s2t_rs = {s1o_fract24[14],|s1o_fract24[13:0]};
      5'd10: s2t_rs = {s1o_fract24[13],|s1o_fract24[12:0]};
      5'd11: s2t_rs = {s1o_fract24[12],|s1o_fract24[11:0]};
      5'd12: s2t_rs = {s1o_fract24[11],|s1o_fract24[10:0]};
      5'd13: s2t_rs = {s1o_fract24[10],|s1o_fract24[ 9:0]};
      5'd14: s2t_rs = {s1o_fract24[ 9],|s1o_fract24[ 8:0]};
      5'd15: s2t_rs = {s1o_fract24[ 8],|s1o_fract24[ 7:0]};
      5'd16: s2t_rs = {s1o_fract24[ 7],|s1o_fract24[ 6:0]};
      5'd17: s2t_rs = {s1o_fract24[ 6],|s1o_fract24[ 5:0]};
      5'd18: s2t_rs = {s1o_fract24[ 5],|s1o_fract24[ 4:0]};
      5'd19: s2t_rs = {s1o_fract24[ 4],|s1o_fract24[ 3:0]};
      5'd20: s2t_rs = {s1o_fract24[ 3],|s1o_fract24[ 2:0]};
      5'd21: s2t_rs = {s1o_fract24[ 2],|s1o_fract24[ 1:0]};
      5'd22: s2t_rs = {s1o_fract24[ 1], s1o_fract24[   0]};
      5'd23: s2t_rs = {s1o_fract24[ 0],1'b0};
      default: s2t_rs = 2'd0; // all fractional's bits were shifted in
    endcase
  end // always

  // stage #2 outputs
  //   input related
  reg s2o_infa, s2o_qnan_a, s2o_snan_a;
  //   computation related
  reg        s2o_sign;
  reg [31:0] s2o_int32;
  reg [1:0]  s2o_rs;
  reg        s2o_ovf;

  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
        // input related
      s2o_infa   <= s1t_infa;
      s2o_qnan_a <= s1t_qnan_a;
      s2o_snan_a <= s1t_snan_a;
        // computation related
      s2o_sign  <= s1o_sign;
      s2o_int32 <= s2t_int32;
      s2o_rs    <= s2t_rs;
      s2o_ovf   <= s1o_ovf;
    end // advance
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


  /* Stage #3: rounding and output */

  // rounding mode isn't require pipelinization
  wire rm_nearest = (rmode_i==2'b00);
  wire rm_to_zero = (rmode_i==2'b01);
  wire rm_to_infp = (rmode_i==2'b10);
  wire rm_to_infm = (rmode_i==2'b11);

  wire s3t_g    = s2o_int32[0];
  wire s3t_r    = s2o_rs[1];
  wire s3t_s    = s2o_rs[0];
  wire s3t_lost = s3t_r | s3t_s;

  wire s3t_rnd_up = (rm_nearest & s3t_r & s3t_s) |
                    (rm_nearest & s3t_g & s3t_r & !s3t_s) |
                    (rm_to_infp & !s2o_sign & s3t_lost) |
                    (rm_to_infm &  s2o_sign & s3t_lost);

  wire [31:0] s3t_int32_rnd = s3t_rnd_up ?
    (s2o_int32 + 32'd1) : s2o_int32;

  wire s3t_carry_rnd = s3t_int32_rnd[31];

  wire s3t_ovf = (!s2o_sign & s3t_carry_rnd) | s2o_ovf;

  wire [31:0] s3t_int32 = (s3t_int32_rnd ^ {32{s2o_sign}}) + {31'd0,s2o_sign};

  wire s3t_int32_00 = !s3t_ovf & (!(|s3t_int32));

   // Generate result   
  wire [31:0] s3t_opc;
  assign s3t_opc =
    (s3t_ovf & (!s2o_sign)) ? 32'h7fffffff :
    (s3t_ovf &   s2o_sign ) ? 32'h80000000 :
                              s3t_int32;

   // Output Register
  always @(posedge clk) begin
    if(adv_i) begin
      out_o <= s3t_opc;
      nan_o <= s2o_snan_a;  // Only signal sNaN
      ine_o <= s3t_lost;
      inv_o <= s3t_ovf;
      unf_o <= s3t_int32_00 & s3t_lost;
      zer_o <= s3t_int32_00;
    end
  end // posedge clock

  // ready is special case
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      ready_o <= 0;
    else if(flush_i)
      ready_o <= 0;
    else if(adv_i)
      ready_o <= s2o_ready;
  end // posedge clock


endmodule // pfpu32_f2i
