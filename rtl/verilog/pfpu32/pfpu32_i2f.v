/////////////////////////////////////////////////////////////////////
////                                                             ////
////  pfpu32_i2f                                                 ////
////  32-bit integer to floating point converter                 ////
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

module pfpu32_i2f
(
   input             clk,
   input             rst,
   input             flush_i,  // flush pipe
   input             adv_i,    // advance pipe
   input             start_i,  // start conversion
   input      [31:0] opa_i,
   output reg        i2f_rdy_o,       // i2f is ready
   output reg        i2f_sign_o,      // i2f signum
   output reg  [9:0] i2f_exp10_o,     // i2f exponent
   output reg [23:0] i2f_fract24_o,   // i2f fractional
   output reg  [1:0] i2f_rs_o         // i2f round & sticky bits
);

  /*
     Any stage's output is registered.
     Definitions:
       s??o_name - "S"tage number "??", "O"utput
       s??t_name - "S"tage number "??", "T"emporary (internally)
  */

  // signum of input
  wire s1t_signa = opa_i[31];
  // magnitude (tow's complement for negative input)
  wire [31:0] s1t_fract32 =
      (opa_i ^ {32{s1t_signa}}) + {31'd0,s1t_signa};
  // normalization shifts
  reg [4:0] s1t_shrx;
  reg [4:0] s1t_shlx;
  reg       s1t_r, s1t_s; // round,sticky
  // shift goal:
  // 23 22                    0 | r/s makes sense for right shift only
  // |  |                     | |
  // h  fffffffffffffffffffffff | rs
  always @(s1t_fract32) begin
    casez(s1t_fract32)  // synopsys full_case parallel_case
      32'b1???????????????????????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd8,5'd0,s1t_fract32[7],|s1t_fract32[6:0]};
      32'b01??????????????????????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd7,5'd0,s1t_fract32[6],|s1t_fract32[5:0]};
      32'b001?????????????????????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd6,5'd0,s1t_fract32[5],|s1t_fract32[4:0]};
      32'b0001????????????????????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd5,5'd0,s1t_fract32[4],|s1t_fract32[3:0]};
      32'b00001???????????????????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd4,5'd0,s1t_fract32[3],|s1t_fract32[2:0]};
      32'b000001??????????????????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd3,5'd0,s1t_fract32[2],|s1t_fract32[1:0]};
      32'b0000001?????????????????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd2,5'd0,s1t_fract32[1],s1t_fract32[0]};
      32'b00000001????????????????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd1,5'd0,s1t_fract32[0],1'b0};
      32'b000000001???????????????????????: // hidden '1' is in its plase
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd0,1'b0,1'b0};
      32'b0000000001??????????????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd1,1'b0,1'b0};
      32'b00000000001?????????????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd2,1'b0,1'b0};
      32'b000000000001????????????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd3,1'b0,1'b0};
      32'b0000000000001???????????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd4,1'b0,1'b0};
      32'b00000000000001??????????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd5,1'b0,1'b0};
      32'b000000000000001?????????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd6,1'b0,1'b0};
      32'b0000000000000001????????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd7,1'b0,1'b0};
      32'b00000000000000001???????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd8,1'b0,1'b0};
      32'b000000000000000001??????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd9,1'b0,1'b0};
      32'b0000000000000000001?????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd10,1'b0,1'b0};
      32'b00000000000000000001????????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd11,1'b0,1'b0};
      32'b000000000000000000001???????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd12,1'b0,1'b0};
      32'b0000000000000000000001??????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd13,1'b0,1'b0};
      32'b00000000000000000000001?????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd14,1'b0,1'b0};
      32'b000000000000000000000001????????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd15,1'b0,1'b0};
      32'b0000000000000000000000001???????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd16,1'b0,1'b0};
      32'b00000000000000000000000001??????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd17,1'b0,1'b0};
      32'b000000000000000000000000001?????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd18,1'b0,1'b0};
      32'b0000000000000000000000000001????:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd19,1'b0,1'b0};
      32'b00000000000000000000000000001???:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd20,1'b0,1'b0};
      32'b000000000000000000000000000001??:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd21,1'b0,1'b0};
      32'b0000000000000000000000000000001?:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd22,1'b0,1'b0};
      32'b00000000000000000000000000000001:
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd23,1'b0,1'b0};
      32'b00000000000000000000000000000000: // zero case
        {s1t_shrx,s1t_shlx,s1t_r,s1t_s} = {5'd0,5'd0,1'b0,1'b0};
    endcase
  end // always


  // stage #1 outputs
  //   computation related
  reg        s1o_sign;
  reg [31:0] s1o_fract32;
  reg [5:0]  s1o_shr;
  reg [5:0]  s1o_shl;
  reg [1:0]  s1o_rs;

  //   registering
  always @(posedge clk) begin
    if(adv_i) begin
        // computation related
      s1o_sign    <= s1t_signa;
      s1o_fract32 <= s1t_fract32;
      s1o_shr     <= s1t_shrx;
      s1o_shl     <= s1t_shlx;
      s1o_rs      <= {s1t_r,s1t_s};
    end // advance
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


  /* Stage #2: align */

  // fractional
  wire [23:0] s2t_fract24 =
    (|s1o_shr) ? (s1o_fract32 >> s1o_shr) :
                 (s1o_fract32 << s1o_shl);
  // exp
  wire [7:0] s2t_exp8 =
    (|s1o_shr)        ? (8'd150 + s1o_shr) : // 150=127+23
    (|s1o_shl)        ? (8'd150 - s1o_shl) :
    (s1o_fract32[23]) ? (8'd150)           : // "1" is in [23]
                        (8'd0);              // input is zero


  // registering output
  always @(posedge clk) begin
    if(adv_i) begin
        // computation related
      i2f_sign_o    <= s1o_sign;
      i2f_exp10_o   <= {2'd0,s2t_exp8};
      i2f_fract24_o <= s2t_fract24;
      i2f_rs_o      <= s1o_rs;
    end // advance
  end // posedge clock

  // ready is special case
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      i2f_rdy_o <= 0;
    else if(flush_i)
      i2f_rdy_o <= 0;
    else if(adv_i)
      i2f_rdy_o <= s1o_ready;
  end // posedge clock

endmodule // pfpu32_i2f
