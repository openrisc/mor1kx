/////////////////////////////////////////////////////////////////////
//                                                                 //
//    pfpu64_cmp_marocchino                                        //
//    64-bit floating point comparision                            //
//                                                                 //
//    Derived from Rudolf Usselmans work for single precision      //
//                                                                 //
//    Author: Rudolf Usselmann                                     //
//            rudi@asics.ws                                        //
//                                                                 //
//    Modified by Julius Baxter, July, 2010                        //
//                julius.baxter@orsoc.se                           //
//                                                                 //
//    Modified by Andrey Bacherov, 2014, 2015, 2016                //
//                avbacherov@opencores.org                         //
//    Update for mor1kx, bug fixing and further development        //
//    Update for MAROCCHINO pipeline                               //
//      (a) latch comparision result separately from arithmetic    //
//    Extend for double precision FP-operands in MAROCCHINO pipe   //
//                                                                 //
/////////////////////////////////////////////////////////////////////
//                                                                 //
//   Copyright (C) 2000 Rudolf Usselmann                           //
//                      rudi@asics.ws                              //
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

module pfpu64_fcmp_marocchino
(
  // clock and reset
  input              clk,
  input              rst,
  // pipeline controls
  input              pipeline_flush_i,     // flush pipe
  input              padv_wb_i,            // advance output latches
  input              grant_wb_to_fp64_cmp_i,
  // command
  input        [2:0] opc_fp64_cmp_i,
  // data related to operand A
  input              signa_i,
  input              opa_0_i,
  input              infa_i,
  // data related to operand B
  input              signb_i,
  input              opb_0_i,
  input              infb_i,
  // data related to operand A|B
  input              snan_i,
  input              qnan_i,
  input              exp_gt_i,
  input              exp_eq_i,
  input              fract_gt_i,
  input              fract_eq_i,
  // Modes
  input              except_fpu_enable_i,
  input              ctrl_fpu_mask_flags_inv_i,
  input              ctrl_fpu_mask_flags_inf_i,
  // Outputs
  //  # WB-latched
  output reg         wb_fp64_flag_set_o,      // comparison result
  output reg         wb_fp64_flag_clear_o,    // comparison result
  output reg         wb_fp64_cmp_inv_o,       // comparison flag 'invalid'
  output reg         wb_fp64_cmp_inf_o,       // comparison flag 'infinity'
  output reg         wb_fp64_cmp_wb_fpcsr_o,  // update FPCSR
  output reg         wb_except_fp64_cmp_o     // exception by FP32-comparison
);

localparam FP_OPC_SFEQ = 3'b000;
localparam FP_OPC_SFNE = 3'b001;
localparam FP_OPC_SFGT = 3'b010;
localparam FP_OPC_SFGE = 3'b011;
localparam FP_OPC_SFLT = 3'b100;
localparam FP_OPC_SFLE = 3'b101;


////////////////////////////////////////////////////////////////////////
// Exception Logic
wire anan = qnan_i | snan_i;
// Comparison invalid when sNaN in on an equal comparison,
// or any NaN for any other comparison.
wire inv_cmp = (snan_i & (opc_fp64_cmp_i == FP_OPC_SFEQ)) |
               (anan   & (opc_fp64_cmp_i != FP_OPC_SFEQ));


////////////////////////////////////////////////////////////////////////
// Comparison Logic
wire exp_lt   = (~exp_gt_i) & (~exp_eq_i); // in_exp11a  < in_exp11b;
wire fract_lt = (~fract_gt_i) & (~fract_eq_i); // in_fract53a  < in_fract53b;

wire all_zero = opa_0_i & opb_0_i;

reg altb, blta, aeqb;

always @(    qnan_i or     snan_i or    infa_i or infb_i or
            signa_i or    signb_i or
           exp_eq_i or   exp_gt_i or    exp_lt or
         fract_eq_i or fract_gt_i or  fract_lt or  all_zero) begin
  // synthesis parallel_case full_case
  casez( {    qnan_i,     snan_i,
              infa_i,     infb_i,
             signa_i,    signb_i,
            exp_eq_i,   exp_gt_i,   exp_lt,
          fract_eq_i, fract_gt_i, fract_lt,
            all_zero})
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
always @(altb or blta or aeqb or opc_fp64_cmp_i) begin
  // synthesis parallel_case full_case
  case(opc_fp64_cmp_i)
    FP_OPC_SFEQ: cmp_flag = aeqb;
    FP_OPC_SFNE: cmp_flag = ~aeqb;
    FP_OPC_SFGT: cmp_flag = blta & ~aeqb;
    FP_OPC_SFGE: cmp_flag = blta | aeqb;
    FP_OPC_SFLT: cmp_flag = altb & ~aeqb;
    FP_OPC_SFLE: cmp_flag = altb | aeqb;
    default:     cmp_flag = 1'b0;
  endcase // case (fpu_op_r)
end // always@ *


////////////////////////////////////////////////////////////////////////
// Just before latching
//  # access to WB
wire exec_fp64_cmp_wb     = grant_wb_to_fp64_cmp_i;
//  # set/slear commands
wire exec_fp64_flag_set   = exec_fp64_cmp_wb &   cmp_flag;
wire exec_fp64_flag_clear = exec_fp64_cmp_wb & (~cmp_flag);
//  # FP32 comparison flags
wire exec_fp64_cmp_inv    = exec_fp64_cmp_wb & ctrl_fpu_mask_flags_inv_i & inv_cmp;
wire exec_fp64_cmp_inf    = exec_fp64_cmp_wb & ctrl_fpu_mask_flags_inf_i & (infa_i | infb_i);
//  # FP32 comparison exception
wire exec_except_fp64_cmp = except_fpu_enable_i & (exec_fp64_cmp_inv | exec_fp64_cmp_inf);


////////////////////////////////////////////////////////////////////////
// WB latches: flag set/clear; fp-related flags; exception
always @(posedge clk `OR_ASYNC_RST) begin
  if (rst) begin
    // comparison results
    wb_fp64_flag_set_o   <= 1'b0;
    wb_fp64_flag_clear_o <= 1'b0;
    // comparison flags
    wb_fp64_cmp_inv_o    <= 1'b0;
    wb_fp64_cmp_inf_o    <= 1'b0;
    // comparison exception
    wb_except_fp64_cmp_o <= 1'b0;
  end
  else if(pipeline_flush_i) begin
    // comparison results
    wb_fp64_flag_set_o   <= 1'b0;
    wb_fp64_flag_clear_o <= 1'b0;
    // comparison flags
    wb_fp64_cmp_inv_o    <= 1'b0;
    wb_fp64_cmp_inf_o    <= 1'b0;
    // comparison exception
    wb_except_fp64_cmp_o <= 1'b0;
  end
  else if(padv_wb_i) begin
    // comparison results
    wb_fp64_flag_set_o   <= exec_fp64_flag_set;
    wb_fp64_flag_clear_o <= exec_fp64_flag_clear;
    // comparison flags
    wb_fp64_cmp_inv_o    <= exec_fp64_cmp_inv;
    wb_fp64_cmp_inf_o    <= exec_fp64_cmp_inf;
    // comparison exception
    wb_except_fp64_cmp_o <= exec_except_fp64_cmp;
  end // advance WB latches
end // posedge clock

////////////////////////////////////////////////////////////////////////
// WB latches: update FPCSR (1-clock to prevent extra writes into FPCSR)
always @(posedge clk `OR_ASYNC_RST) begin
  if (rst)
    wb_fp64_cmp_wb_fpcsr_o <= 1'b0;
  else if (pipeline_flush_i)
    wb_fp64_cmp_wb_fpcsr_o <= 1'b0;
  else if (padv_wb_i)
    wb_fp64_cmp_wb_fpcsr_o <= exec_fp64_cmp_wb;
  else
    wb_fp64_cmp_wb_fpcsr_o <= 1'b0;
end // @clock

endmodule // pfpu64_fcmp_marocchino
