/////////////////////////////////////////////////////////////////////
////                                                             ////
////  pfpu32_cmp_marocchino                                      ////
////  32-bit floating point comparision                          ////
////                                                             ////
////  Author: Rudolf Usselmann                                   ////
////          rudi@asics.ws                                      ////
////                                                             ////
////  Modified by Julius Baxter, July, 2010                      ////
////              julius.baxter@orsoc.se                         ////
////                                                             ////
////  Update for mor1kx, bug fixing and further development      ////
////  Update for MAROCCHINO pipeline                             ////
////    (a) latch comparision result separately from arithmetic  ////
////              Andrey Bacherov, 2014, 2015                    ////
////              avbacherov@opencores.org                       ////
////                                                             ////
/////////////////////////////////////////////////////////////////////
////                                                             ////
//// Copyright (C) 2000 Rudolf Usselmann                         ////
////                    rudi@asics.ws                            ////
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

module pfpu32_fcmp_marocchino
(
  // clocks, resets and other controls
  input                               clk,
  input                               rst,
  input                               flush_i,  // flush pipe
  input                               padv_wb_i,// advance output latches
  input                               grant_wb_to_1clk_i,
  // command
  input                               fpu_op_is_comp_i,
  input       [`OR1K_FPUOP_WIDTH-1:0] cmp_type_i,
  // Operands
  input                        [31:0] rfa_i,
  input                        [31:0] rfb_i,
  // WB latches
  output reg                          wb_fp32_flag_set_o,   // comparison result
  output reg                          wb_fp32_flag_clear_o, // comparison result
  output reg  [`OR1K_FPCSR_WIDTH-1:0] wb_fp32_cmp_fpcsr_o   // comparison exceptions
);

////////////////////////////////////////////////////////////////////////
// Input operand analysis

// analysis of input values
//   split input a
wire        in_signa  = rfa_i[31];
wire  [7:0] in_expa   = rfa_i[30:23];
wire [22:0] in_fracta = rfa_i[22:0];
//   detect infinity a
wire in_expa_ff = &in_expa;
wire in_infa    = in_expa_ff & (~(|in_fracta));
//   signaling NaN: exponent is 8hff, [22] is zero,
//                  rest of fract is non-zero
//   quiet NaN: exponent is 8hff, [22] is 1
wire in_snan_a = in_expa_ff & (~in_fracta[22]) & (|in_fracta[21:0]);
wire in_qnan_a = in_expa_ff &   in_fracta[22];
//   denormalized/zero of a
wire in_opa_0  = ~(|rfa_i[30:0]);
wire in_opa_dn = (~(|in_expa)) & (|in_fracta);

//   split input b
wire        in_signb  = rfb_i[31];
wire  [7:0] in_expb   = rfb_i[30:23];
wire [22:0] in_fractb = rfb_i[22:0];
//   detect infinity b
wire in_expb_ff = &in_expb;
wire in_infb    = in_expb_ff & (~(|in_fractb));
//   detect NaNs in b
wire in_snan_b = in_expb_ff & (~in_fractb[22]) & (|in_fractb[21:0]);
wire in_qnan_b = in_expb_ff &   in_fractb[22];
//   denormalized/zero of a
wire in_opb_0  = ~(|rfb_i[30:0]);
wire in_opb_dn = (~(|in_expb)) & (|in_fractb);

// restored exponents
wire [9:0] in_exp10a = {2'd0,in_expa[7:1],(in_expa[0] | in_opa_dn)};
wire [9:0] in_exp10b = {2'd0,in_expb[7:1],(in_expb[0] | in_opb_dn)};
// restored fractionals
wire [23:0] in_fract24a = {((~in_opa_dn) & (~in_opa_0)),in_fracta};
wire [23:0] in_fract24b = {((~in_opb_dn) & (~in_opb_0)),in_fractb};


////////////////////////////////////////////////////////////////////////
// Exception Logic
wire qnan = in_qnan_a | in_qnan_b;
wire snan = in_snan_a | in_snan_b;
wire anan = qnan | snan;
// Comparison invalid when sNaN in on an equal comparison,
// or any NaN for any other comparison.
wire inv_cmp = (snan & (cmp_type_i == `OR1K_FPCOP_SFEQ)) |
               (anan & (cmp_type_i != `OR1K_FPCOP_SFEQ));


////////////////////////////////////////////////////////////////////////
// Comparison Logic
wire exp_gt = in_exp10a  > in_exp10b;
wire exp_eq = in_exp10a == in_exp10b;
wire exp_lt = (~exp_gt) & (~exp_eq); // in_exp10a  < in_exp10b;

wire fract_gt = in_fract24a  > in_fract24b;
wire fract_eq = in_fract24a == in_fract24b;
wire fract_lt = (~fract_gt) & (~fract_eq); // in_fract24a  < in_fract24b;

wire all_zero = in_opa_0 & in_opb_0;

reg altb, blta, aeqb;

always @( qnan or snan or in_infa or in_infb or in_signa or in_signb or
          exp_eq or exp_gt or exp_lt or
          fract_eq or fract_gt or fract_lt or all_zero) begin

  casez( {qnan, snan, in_infa, in_infb, in_signa, in_signb,
          exp_eq, exp_gt, exp_lt,
          fract_eq, fract_gt, fract_lt, all_zero})
    13'b1?_??_??_???_???_?: {blta, altb, aeqb} = 3'b000; // qnan
    13'b?1_??_??_???_???_?: {blta, altb, aeqb} = 3'b000; // snan

    13'b00_11_00_???_???_?: {blta, altb, aeqb} = 3'b001; // both op INF comparisson
    13'b00_11_01_???_???_?: {blta, altb, aeqb} = 3'b100;
    13'b00_11_10_???_???_?: {blta, altb, aeqb} = 3'b010;
    13'b00_11_11_???_???_?: {blta, altb, aeqb} = 3'b001;

    13'b00_10_00_???_???_?: {blta, altb, aeqb} = 3'b100; // opa_i INF comparisson
    13'b00_10_01_???_???_?: {blta, altb, aeqb} = 3'b100;
    13'b00_10_10_???_???_?: {blta, altb, aeqb} = 3'b010;
    13'b00_10_11_???_???_?: {blta, altb, aeqb} = 3'b010;

    13'b00_01_00_???_???_?: {blta, altb, aeqb} = 3'b010; // opb_i INF comparisson
    13'b00_01_01_???_???_?: {blta, altb, aeqb} = 3'b100;
    13'b00_01_10_???_???_?: {blta, altb, aeqb} = 3'b010;
    13'b00_01_11_???_???_?: {blta, altb, aeqb} = 3'b100;

    13'b00_00_10_???_???_0: {blta, altb, aeqb} = 3'b010; //compare base on sign
    13'b00_00_01_???_???_0: {blta, altb, aeqb} = 3'b100; //compare base on sign

    13'b00_00_??_???_???_1: {blta, altb, aeqb} = 3'b001; //compare base on sign both are zero

    13'b00_00_00_010_???_?: {blta, altb, aeqb} = 3'b100; // cmp exp, equal sign
    13'b00_00_00_001_???_?: {blta, altb, aeqb} = 3'b010;
    13'b00_00_11_010_???_?: {blta, altb, aeqb} = 3'b010;
    13'b00_00_11_001_???_?: {blta, altb, aeqb} = 3'b100;

    13'b00_00_00_100_010_?: {blta, altb, aeqb} = 3'b100; // compare fractions, equal sign, equal exp
    13'b00_00_00_100_001_?: {blta, altb, aeqb} = 3'b010;
    13'b00_00_11_100_010_?: {blta, altb, aeqb} = 3'b010;
    13'b00_00_11_100_001_?: {blta, altb, aeqb} = 3'b100;

    13'b00_00_00_100_100_?: {blta, altb, aeqb} = 3'b001;
    13'b00_00_11_100_100_?: {blta, altb, aeqb} = 3'b001;

    default: {blta, altb, aeqb} = 3'b000;
  endcase
end // @ clock


////////////////////////////////////////////////////////////////////////
// Comparison cmp_flag generation
reg cmp_flag;
always @(altb or blta or aeqb or cmp_type_i) begin
  case(cmp_type_i)
    `OR1K_FPCOP_SFEQ: cmp_flag = aeqb;
    `OR1K_FPCOP_SFNE: cmp_flag = ~aeqb;
    `OR1K_FPCOP_SFGT: cmp_flag = blta & ~aeqb;
    `OR1K_FPCOP_SFGE: cmp_flag = blta | aeqb;
    `OR1K_FPCOP_SFLT: cmp_flag = altb & ~aeqb;
    `OR1K_FPCOP_SFLE: cmp_flag = altb | aeqb;
    default:          cmp_flag = 1'b0;
  endcase // case (fpu_op_r)
end // always@ *


////////////////////////////////////////////////////////////////////////
// WB latches
always @(posedge clk `OR_ASYNC_RST) begin
  if (rst) begin
    wb_fp32_flag_set_o   <= 1'b0;
    wb_fp32_flag_clear_o <= 1'b0;
    wb_fp32_cmp_fpcsr_o  <= {`OR1K_FPCSR_WIDTH{1'b0}};
  end
  else if(flush_i) begin
    wb_fp32_flag_set_o   <= 1'b0;
    wb_fp32_flag_clear_o <= 1'b0;
    wb_fp32_cmp_fpcsr_o  <= {`OR1K_FPCSR_WIDTH{1'b0}};
  end
  else if(padv_wb_i) begin
    if (fpu_op_is_comp_i & grant_wb_to_1clk_i) begin
      // comparison results
      wb_fp32_flag_set_o   <= cmp_flag;
      wb_fp32_flag_clear_o <= ~cmp_flag;
      // exeptions
      wb_fp32_cmp_fpcsr_o[`OR1K_FPCSR_IVF] <= inv_cmp;
      wb_fp32_cmp_fpcsr_o[`OR1K_FPCSR_INF] <= in_infa | in_infb;
    end
    else begin
      // comparison results
      wb_fp32_flag_set_o   <= 1'b0;
      wb_fp32_flag_clear_o <= 1'b0;
      // exeptions
      wb_fp32_cmp_fpcsr_o[`OR1K_FPCSR_IVF] <= 1'b0;
      wb_fp32_cmp_fpcsr_o[`OR1K_FPCSR_INF] <= 1'b0;
    end // comp-op / not
  end // advance WB latches
end // posedge clock

endmodule // pfpu32_fcmp_marocchino
