//////////////////////////////////////////////////////////////////////
////                                                              ////
////  mor1kx's FPU Wrapper                                        ////
////                                                              ////
////  This file is part of the mor1kx project                     ////
////  (an implementation of OpenRISC 1K architecture)             ////
////  https://github.com/openrisc/mor1kx                          ////
////                                                              ////
////  Description                                                 ////
////  Wrapper for floating point unit.                            ////
////                                                              ////
////  Author(s):                                                  ////
////      - Julius Baxter, julius@opencores.org                   ////
////        Initial design fo OpenRISC 1200                       ////
////        http://opencores.org/project,or1k                     ////
////                                                              ////
////      - Andrey Bacherov, 2014, avbacherov@opencores.org       ////
////        Port for mor1kx's cappuccino pipeline                 ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2009,2010 Authors and OPENCORES.ORG            ////
////                                                              ////
//// This source file may be used and distributed without         ////
//// restriction provided that this copyright statement is not    ////
//// removed from the file and that any derivative work contains  ////
//// the original copyright notice and the associated disclaimer. ////
////                                                              ////
//// This source file is free software; you can redistribute it   ////
//// and/or modify it under the terms of the GNU Lesser General   ////
//// Public License as published by the Free Software Foundation; ////
//// either version 2.1 of the License, or (at your option) any   ////
//// later version.                                               ////
////                                                              ////
//// This source is distributed in the hope that it will be       ////
//// useful, but WITHOUT ANY WARRANTY; without even the implied   ////
//// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      ////
//// PURPOSE.  See the GNU Lesser General Public License for more ////
//// details.                                                     ////
////                                                              ////
//// You should have received a copy of the GNU Lesser General    ////
//// Public License along with this source; if not, download it   ////
//// from http://www.opencores.org/lgpl.shtml                     ////
////                                                              ////
//////////////////////////////////////////////////////////////////////


`include "mor1kx-defines.v"

module mor1kx_fpu_top
#(
  parameter OPTION_OPERAND_WIDTH = 32
)
(
  input clk,
  input rst,
  input decode_valid_i,
  input [`OR1K_FPUOP_WIDTH-1:0]    op_fpu_i,
  input [`OR1K_FPCSR_RM_SIZE-1:0]  fpu_round_mode_i,
  input [OPTION_OPERAND_WIDTH-1:0] rfa_i,
  input [OPTION_OPERAND_WIDTH-1:0] rfb_i,
  output is_op_fpu_o,
  output fpu_valid_o,
  output [OPTION_OPERAND_WIDTH-1:0] fpu_result_o,
  output [`OR1K_FPCSR_WIDTH-1:0] fpcsr_o,
  output fpu_cmp_flag_o,
  output fpu_op_is_comp_o,
  output fpu_cmp_valid_o
);

wire [`OR1K_FPUOP_WIDTH-1:0] opc_fpu; // alias for op_fpu_i with dropped MSB
wire fpu_new_input;
wire fpu_op_is_arith, fpu_op_is_conv, fpu_op_is_comp;
wire fpu_arith_done, fpu_conv_done;
wire [OPTION_OPERAND_WIDTH-1:0] result_arith, result_conv;
wire inf, inv_inf_op_in,snan, snan_in,qnan, 
     ine, overflow, underflow, zero, dbz, 
     dbz_in, mul_z_inf, nan_in;
wire altb, blta, aeqb, inf_cmp, zero_cmp, 
     unordered;
wire snan_conv, ine_conv, inv_conv, 
     zero_conv, underflow_conv, 
     overflow_conv;
wire inv_comp;   

// MSB (set by decode stage) indicates FPU instruction
// Get rid of top bit - is FPU op valid bit
wire   is_op_fpu = op_fpu_i[`OR1K_FPUOP_WIDTH-1];
assign opc_fpu  = {1'b0,op_fpu_i[`OR1K_FPUOP_WIDTH-2:0]};

assign fpu_new_input = decode_valid_i & is_op_fpu;

assign fpu_op_is_arith = is_op_fpu & (!(|op_fpu_i[3:2]));
assign fpu_op_is_conv  = is_op_fpu & (op_fpu_i[2] & !op_fpu_i[3]);   
assign fpu_op_is_comp  = is_op_fpu & op_fpu_i[3];

assign fpu_valid = !decode_valid_i &
                   ((fpu_op_is_arith & fpu_arith_done) |
                    (fpu_op_is_conv  & fpu_conv_done)  |
                    fpu_op_is_comp);
                          
wire   fpu_cmp_valid = !decode_valid_i; // for fpu flag set/clear logic

// Prepare flags fo FPCSR
assign fpcsr_o[`OR1K_FPCSR_OVF] = (overflow & fpu_op_is_arith);
assign fpcsr_o[`OR1K_FPCSR_UNF] = (underflow & fpu_op_is_arith) |
                                  (underflow_conv  & fpu_op_is_conv);
assign fpcsr_o[`OR1K_FPCSR_SNF] = (snan  & fpu_op_is_arith)|
                                  (snan_conv & fpu_op_is_conv);
assign fpcsr_o[`OR1K_FPCSR_QNF] = (qnan  & fpu_op_is_arith);
assign fpcsr_o[`OR1K_FPCSR_ZF]  = (zero  & fpu_op_is_arith) | 
                                  (zero_cmp & fpu_op_is_comp) |
                                  (zero_conv & fpu_op_is_conv);
assign fpcsr_o[`OR1K_FPCSR_IXF] = (ine  & fpu_op_is_arith) |
                                  (ine_conv & fpu_op_is_conv);
assign fpcsr_o[`OR1K_FPCSR_IVF] = ((snan_in | dbz_in | inv_inf_op_in | mul_z_inf) & fpu_op_is_arith) |
                                  ((inv_conv | snan_conv) & fpu_op_is_conv) |
                                  (inv_comp & fpu_op_is_comp);
assign fpcsr_o[`OR1K_FPCSR_INF] = (inf  & fpu_op_is_arith) | 
                                  (inf_cmp & fpu_op_is_comp);
assign fpcsr_o[`OR1K_FPCSR_DZF] = (dbz & fpu_op_is_arith);
assign fpcsr_o[`OR1K_FPCSR_RM]  = {`OR1K_FPCSR_RM_SIZE{1'b0}}; // just fill it : doesn't affect spr in ctrl
assign fpcsr_o[`OR1K_FPCSR_FPEE]= 0; // just fill it : doesn't affect spr in ctrl

// Comparison fpu_cmp_flag generation
reg fpu_cmp_flag;
always @*
  begin
    case(opc_fpu)
      `OR1K_FPCOP_SFEQ: fpu_cmp_flag = aeqb;
      `OR1K_FPCOP_SFNE: fpu_cmp_flag = !aeqb;
      `OR1K_FPCOP_SFGT: fpu_cmp_flag = blta & !aeqb;
      `OR1K_FPCOP_SFGE: fpu_cmp_flag = blta | aeqb;
      `OR1K_FPCOP_SFLT: fpu_cmp_flag = altb & !aeqb;
      `OR1K_FPCOP_SFLE: fpu_cmp_flag = altb | aeqb;
      default:          fpu_cmp_flag = 0;
    endcase // case (fpu_op_r)
  end // always@ *


// MUX for outputs from arith and conversion modules
wire [OPTION_OPERAND_WIDTH-1:0] fpu_result;
assign fpu_result = fpu_op_is_conv  ? result_conv : 
                    fpu_op_is_arith ? result_arith : 
                    {OPTION_OPERAND_WIDTH{1'b0}};   
   
// FPU 100 VHDL core from OpenCores.org: http://opencores.org/project,fpu100
// Used only for add,sub,mul,div
mor1kx_fpu_arith fpu_arith
(
  .clk(clk),
  .rst(rst),
  .opa_i(rfa_i),
  .opb_i(rfb_i),
  .fpu_op_i({1'b0,opc_fpu[1:0]}), // Only bottom 2 bits
  .rmode_i(fpu_round_mode_i),
  .output_o(result_arith),
  .clr_ready_flag_i(fpu_new_input),
  .start_i(decode_valid_i & fpu_op_is_arith),
  .ready_o(fpu_arith_done),
  .ine_o(ine),
  .overflow_o(overflow),
  .underflow_o(underflow),
  .div_zero_o(dbz),
  .inf_o(inf),
  .zero_o(zero),
  .qnan_o(qnan),
  .snan_o(snan)
);

// Logic for detection of signaling NaN on input
// signaling NaN: exponent is 8hff, [22] is zero, rest of fract is non-zero
// quiet NaN: exponent is 8hff, [22] is 1
reg a_is_snan, b_is_snan;
reg a_is_qnan, b_is_qnan;

always @(posedge clk `OR_ASYNC_RST)
  if (rst) begin
    a_is_snan <= 0;
    b_is_snan <= 0;
    a_is_qnan <= 0;
    b_is_qnan <= 0;
  end
  else begin
    a_is_snan <= (rfa_i[30:23]==8'hff) & !rfa_i[22] & (|rfa_i[21:0]);
    b_is_snan <= (rfb_i[30:23]==8'hff) & !rfb_i[22] & (|rfb_i[21:0]);
    a_is_qnan <= (rfa_i[30:23]==8'hff) & rfa_i[22];
    b_is_qnan <= (rfb_i[30:23]==8'hff) & rfb_i[22];
  end
// Signal to indicate there was rfa_i signaling NaN on input
assign snan_in = a_is_snan | b_is_snan;

// Check for, add with opposite signed infinities, or subtract with 
// same signed infinities.
reg a_is_inf, b_is_inf, a_b_sign_xor;

always @(posedge clk `OR_ASYNC_RST)
  if (rst) begin
    a_is_inf <= 0;
    b_is_inf <= 0;
    a_b_sign_xor <= 0;
  end
  else begin
    a_is_inf <= (rfa_i[30:23]==8'hff) & !(|rfa_i[22:0]);
    b_is_inf <= (rfb_i[30:23]==8'hff) & !(|rfb_i[22:0]);
    a_b_sign_xor <= rfa_i[31] ^ rfb_i[31];
  end

assign inv_inf_op_in = (a_is_inf & b_is_inf) & 
         ((a_b_sign_xor & (opc_fpu == `OR1K_FPUOP_ADD)) |
          (!a_b_sign_xor & (opc_fpu == `OR1K_FPUOP_SUB)) |
          (opc_fpu == `OR1K_FPUOP_DIV)); // inf/inf

// Check if it's 0.0/0.0 to generate invalid signal (ignore sign bit)
reg a_is_zero, b_is_zero;   
always @(posedge clk `OR_ASYNC_RST)
  if (rst) begin
    a_is_zero <= 0;
    b_is_zero <= 0;
  end
  else begin
    a_is_zero <= !(|rfa_i[30:0]);
    b_is_zero <= !(|rfb_i[30:0]);
  end

assign dbz_in = (opc_fpu == `OR1K_FPUOP_DIV) &
                (a_is_zero & b_is_zero);

assign mul_z_inf = (opc_fpu == `OR1K_FPUOP_MUL) & 
                   ((a_is_zero & b_is_inf) | (b_is_zero & a_is_inf));

assign nan_in = (a_is_snan | b_is_snan | a_is_qnan | b_is_qnan);

// 32-bit integer <-> single precision floating point conversion unit
mor1kx_fpu_intfloat_conv fpu_intfloat_conv
(
  .clk(clk),
  .rst(rst),
  .rmode(fpu_round_mode_i),
  .fpu_op(opc_fpu[2:0]),
  .opa(rfa_i), // will be registered internally
  .clr_ready_flag_i(fpu_new_input),
  .start_i(decode_valid_i & fpu_op_is_conv),
  .out(result_conv),
  .ready_o(fpu_conv_done),
  .snan(snan_conv),
  .ine(ine_conv),
  .inv(inv_conv),
  .overflow(overflow_conv),
  .underflow(underflow_conv),
  .zero(zero_conv)
);

// Single precision floating point number comparison module
mor1kx_fpu_fcmp fpu_fcmp
(
  .clk(clk),
  .rst(rst),
  .opa(rfa_i), 
  .opb(rfb_i),
  .unordered_o(unordered),
   // I am convinced the comparison logic is wrong way around in this 
   // module, simplest to swap them on output -- julius       
  .altb_o(blta), 
  .blta_o(altb), 
  .aeqb_o(aeqb), 
  .inf_o(inf_cmp), 
  .zero_o(zero_cmp)
);

// Comparison invalid when sNaN in on an equal comparison, or any NaN 
// for any other comparison.
assign inv_comp =  (snan_in & (opc_fpu == `OR1K_FPCOP_SFEQ)) | 
                   (nan_in &  (opc_fpu != `OR1K_FPCOP_SFEQ));

// form output
assign is_op_fpu_o = is_op_fpu;
assign fpu_valid_o = fpu_valid;
assign fpu_result_o = fpu_result;
assign fpu_cmp_flag_o = fpu_cmp_flag;
assign fpu_op_is_comp_o = fpu_op_is_comp;
assign fpu_cmp_valid_o = fpu_cmp_valid;

endmodule // mor1kx_fpu_top
