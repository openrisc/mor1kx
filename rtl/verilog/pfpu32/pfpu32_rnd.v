/////////////////////////////////////////////////////////////////////
////                                                             ////
////  pfpu32_rnd                                                 ////
////  32-bit common rounding module for FPU                      ////
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

module pfpu32_rnd
(
  // clocks, resets and other controls
  input        clk,
  input        rst,
  input        flush_i,  // flush pipe
  input        adv_i,    // advance pipe
  input  [1:0] rmode_i,  // rounding mode
  // input from add/sub
  input        add_rdy_i,       // add/sub is ready
  input        add_sign_i,      // add/sub signum
  input  [9:0] add_exp10_i,     // add/sub exponent
  input [23:0] add_fract24_i,   // add/sub fractional
  input  [1:0] add_rs_i,        // add/sub round & sticky bits
  input        add_inv_i,       // add/sub invalid operation flag
  input        add_inf_i,       // add/sub infinity input
  input        add_snan_i,      // add/sub signaling NaN input
  input        add_qnan_i,      // add/sub quiet NaN input
  input        add_anan_sign_i, // add/sub signum for output nan
  // input from mul
  input        mul_rdy_i,       // mul is ready
  input        mul_sign_i,      // mul signum
  input  [9:0] mul_exp10_i,     // mul exponent
  input [23:0] mul_fract24_i,   // mul fractional
  input  [1:0] mul_rs_i,        // mul round & sticky bits
  input        mul_inv_i,       // mul invalid operation flag
  input        mul_inf_i,       // mul infinity input
  input        mul_snan_i,      // mul signaling NaN input
  input        mul_qnan_i,      // mul quiet NaN input
  input        mul_anan_sign_i, // mul signum for output nan
  // input from div
  input        div_rdy_i,       // div is ready
  input        div_sign_i,      // div signum
  input  [9:0] div_exp10_i,     // div exponent
  input [23:0] div_fract24_i,   // div fractional
  input  [1:0] div_rs_i,        // div round & sticky bits
  input        div_inv_i,       // div invalid operation flag
  input        div_inf_i,       // div infinity input
  input        div_snan_i,      // div signaling NaN input
  input        div_qnan_i,      // div quiet NaN input
  input        div_anan_sign_i, // div signum for output nan
  input        div_dbz_i,       // div division by zero flag
  input        div_dbinf_i,     // div division by infinity
  // input from i2f
  input        i2f_rdy_i,       // i2f is ready
  input        i2f_sign_i,      // i2f signum
  input  [9:0] i2f_exp10_i,     // i2f exponent
  input [23:0] i2f_fract24_i,   // i2f fractional
  input  [1:0] i2f_rs_i,        // i2f round & sticky bits
  // input from f2i
  input        f2i_rdy_i,       // f2i is ready
  input        f2i_sign_i,      // f2i signum
  input [31:0] f2i_int32_i,     // f2i i32 modulo
  input  [1:0] f2i_rs_i,        // f2i round & sticky bits
  input        f2i_ovf_i,       // f2i overflow flag
  input        f2i_snan_i,      // f2i signaling NaN input
  // input from cmp
  input        cmp_rdy_i,       // cmp is ready
  input        cmp_res_i,       // cmp result
  input        cmp_inv_i,       // cmp invalid flag
  input        cmp_inf_i,       // cmp infinity flag
  // outputs
  output reg                  [31:0] fpu_result_o,
  output reg                         fpu_valid_o,
  output reg                         fpu_cmp_flag_o,
  output reg                         fpu_cmp_valid_o,
  output reg [`OR1K_FPCSR_WIDTH-1:0] fpcsr_o
);

  localparam INF  = 31'b1111111100000000000000000000000;
  localparam QNAN = 31'b1111111110000000000000000000000;
  localparam SNAN = 31'b1111111101111111111111111111111;

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

  /* Stage #1: input multiplexer */

  wire        s1t_sign;
  wire  [9:0] s1t_exp10;
  wire [31:0] s1t_fract32;
  wire  [1:0] s1t_rs;
  wire        s1t_inv;
  wire        s1t_inf;  
  wire        s1t_snan;
  wire        s1t_qnan;
  wire        s1t_anan_sign;

  assign {s1t_sign,s1t_exp10,s1t_fract32,s1t_rs,s1t_inv,s1t_inf,s1t_snan,s1t_qnan,s1t_anan_sign} =
    add_rdy_i ? {add_sign_i,add_exp10_i,{8'd0,add_fract24_i},add_rs_i,add_inv_i,add_inf_i,add_snan_i,add_qnan_i,add_anan_sign_i} :
    mul_rdy_i ? {mul_sign_i,mul_exp10_i,{8'd0,mul_fract24_i},mul_rs_i,mul_inv_i,mul_inf_i,mul_snan_i,mul_qnan_i,mul_anan_sign_i} :
    div_rdy_i ? {div_sign_i,div_exp10_i,{8'd0,div_fract24_i},div_rs_i,div_inv_i,div_inf_i,div_snan_i,div_qnan_i,div_anan_sign_i} :
    i2f_rdy_i ? {i2f_sign_i,i2f_exp10_i,{8'd0,i2f_fract24_i},i2f_rs_i,1'b0,1'b0,1'b0,1'b0,1'b0} :
    f2i_rdy_i ? {f2i_sign_i,10'd0,f2i_int32_i,f2i_rs_i,1'b0,1'b0,f2i_snan_i,1'b0,f2i_sign_i} :
                {1'b0,10'd0,32'd0,2'd0,1'b0,1'b0,1'b0,1'b0,1'b0};

  wire s1t_g    = s1t_fract32[0];
  wire s1t_r    = s1t_rs[1];
  wire s1t_s    = s1t_rs[0];
  wire s1t_lost = s1t_r | s1t_s;

  wire s1t_rnd_up = (rm_nearest & s1t_r & s1t_s) |
                    (rm_nearest & s1t_g & s1t_r & !s1t_s) |
                    (rm_to_infp & !s1t_sign & s1t_lost) |
                    (rm_to_infm &  s1t_sign & s1t_lost);

  // 1rst stage output
  reg        s1o_rdy;
  reg        s1o_sign;
  reg  [9:0] s1o_exp10;
  reg [31:0] s1o_fract32;
  reg        s1o_lost;
  reg        s1o_inv;
  reg        s1o_inf;  
  reg        s1o_snan_i;
  reg        s1o_qnan_i;
  reg        s1o_anan_sign_i;
  reg        s1o_dbz, s1o_dbinf, s1o_f2i_ovf, s1o_f2i;
  // registering
  always @(posedge clk) begin
    if(adv_i) begin
      s1o_sign    <= s1t_sign;
      s1o_exp10   <= s1t_exp10;
      s1o_fract32 <= s1t_fract32 + {31'd0,s1t_rnd_up};
      s1o_lost    <= s1t_lost;
      s1o_dbz     <= div_dbz_i & div_rdy_i;
      s1o_dbinf   <= div_dbinf_i & div_rdy_i;
      s1o_f2i_ovf <= f2i_ovf_i;
      s1o_f2i     <= f2i_rdy_i;
      //...
      s1o_inv     <= s1t_inv;
      s1o_inf     <= s1t_inf;      
      s1o_snan_i  <= s1t_snan;
      s1o_qnan_i  <= s1t_qnan;
      s1o_anan_sign_i <= s1t_anan_sign;
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
      s1o_ready <= (add_rdy_i | mul_rdy_i | div_rdy_i | i2f_rdy_i | f2i_rdy_i);
  end // posedge clock


  /* Stage #2: finish */


  // floating point output
  wire s2t_f32_shr = s1o_fract32[24];
  // update exponent and fraction
  wire [9:0]  s2t_f32_exp10   = s1o_exp10 + {9'd0,s2t_f32_shr};
  wire [23:0] s2t_f32_fract24 = s2t_f32_shr ? s1o_fract32[24:1] :
                                              s1o_fract32[23:0];
   // potentially denormalized
  wire s2t_f32_fract24_dn = !s2t_f32_fract24[23];
   // potentially zero
  wire s2t_f32_fract24_00 = !(|s2t_f32_fract24);


  // integer output (f2i)
  wire s3t_i32_carry_rnd = s1o_fract32[31];
  wire s3t_i32_inv = (!s1o_sign & s3t_i32_carry_rnd) | s1o_f2i_ovf;
  // two's complement for negative number
  wire [31:0] s3t_i32_int32 = (s1o_fract32 ^ {32{s1o_sign}}) + {31'd0,s1o_sign};
  // zero
  wire s3t_i32_int32_00 = !s3t_i32_inv & (!(|s3t_i32_int32));
  // int32 output
  wire [31:0] s3t_i32_opc;
  assign s3t_i32_opc =
    s3t_i32_inv ? (32'h7fffffff ^ {32{s1o_sign}}) : s3t_i32_int32;


   // Generate result and flags
  wire s2t_ine, s2t_ovf, s2t_inf, s2t_unf, s2t_zer;
  wire [31:0] s2t_opc;
  assign {s2t_opc,s2t_ine,s2t_ovf,s2t_inf,s2t_unf,s2t_zer} =
    // f2i
    s1o_f2i ?       // ine  ovf  inf               unf                 zer
      {s3t_i32_opc,s1o_lost,1'b0,1'b0,(s3t_i32_int32_00 & s1o_lost),s3t_i32_int32_00} :
    // qnan output
    (s1o_snan_i | s1o_qnan_i) ? // ine  ovf  inf  unf  zer
      {{s1o_anan_sign_i,QNAN},    1'b0,1'b0,1'b0,1'b0,1'b0} :
    // snan output
    s1o_inv ?        // ine  ovf  inf  unf  zer
      {{s1o_sign,SNAN},1'b0,1'b0,1'b0,1'b0,1'b0} :
    // overflow and infinity
    ((s2t_f32_exp10 > 10'd254) | s1o_inf | s1o_dbz) ? // ine                         ovf  inf  unf  zer
      {{s1o_sign,INF},((s1o_lost | (!s1o_inf)) & (!s1o_dbz)),((!s1o_inf) & (!s1o_dbz)),1'b1,1'b0,1'b0} :
    // zero and underflow
    (s2t_f32_fract24_dn | s2t_f32_fract24_00) ?// ine  ovf  inf               unf                             zer
      {{s1o_sign,8'd0,s2t_f32_fract24[22:0]},s1o_lost,1'b0,1'b0,((s2t_f32_fract24_00 & s1o_lost) | s1o_dbinf),s2t_f32_fract24_00} :
    // normal result                                        ine  ovf  inf  unf  zer
    {s1o_sign,s2t_f32_exp10[7:0],s2t_f32_fract24[22:0],s1o_lost,1'b0,1'b0,1'b0,1'b0};


  // Output Register
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
        // overall FPU results
      fpu_result_o    <= 32'd0;
      fpu_valid_o     <= 1'b0;
        // comparison specials
      fpu_cmp_flag_o  <= 1'b0;
      fpu_cmp_valid_o <= 1'b0;
        // exeptions
      fpcsr_o         <= {`OR1K_FPCSR_WIDTH{1'b0}};
    end
    else if(flush_i) begin
        // overall FPU results
      fpu_result_o    <= 32'd0;
      fpu_valid_o     <= 1'b0;
        // comparison specials
      fpu_cmp_flag_o  <= 1'b0;
      fpu_cmp_valid_o <= 1'b0;
        // exeptions
      fpcsr_o         <= {`OR1K_FPCSR_WIDTH{1'b0}};
    end
    else if(adv_i) begin
        // overall FPU results
      fpu_result_o    <= s2t_opc;
      fpu_valid_o     <= s1o_ready | cmp_rdy_i;
        // comparison specials
      fpu_cmp_flag_o  <= cmp_res_i;
      fpu_cmp_valid_o <= cmp_rdy_i;
        // exeptions
      fpcsr_o[`OR1K_FPCSR_OVF] <= s2t_ovf;
      fpcsr_o[`OR1K_FPCSR_UNF] <= s2t_unf;
      fpcsr_o[`OR1K_FPCSR_SNF] <= s1o_inv | (s1o_snan_i & s1o_f2i);
      fpcsr_o[`OR1K_FPCSR_QNF] <= s1o_qnan_i;
      fpcsr_o[`OR1K_FPCSR_ZF]  <= s2t_zer;
      fpcsr_o[`OR1K_FPCSR_IXF] <= s2t_ine;
      fpcsr_o[`OR1K_FPCSR_IVF] <= (s1o_inv | (s3t_i32_inv & s1o_f2i) | s1o_snan_i) |
                                  (cmp_inv_i & cmp_rdy_i);
      fpcsr_o[`OR1K_FPCSR_INF] <= s2t_inf |
                                  (cmp_inf_i & cmp_rdy_i);
      fpcsr_o[`OR1K_FPCSR_DZF] <= s1o_dbz;
    end
  end // posedge clock

endmodule // pfpu32_rnd
