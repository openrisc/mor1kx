/////////////////////////////////////////////////////////////////////
////                                                             ////
////  pfpu32_top                                                 ////
////  32-bit floating point top level                            ////
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

// fpu operations:
// ==========================
// 0000 = add,
// 0001 = substract,
// 0010 = multiply,
// 0011 = divide,
// 0100 = i2f
// 0101 = f2i
// 0110 = unused (rem)
// 0111 = reserved
// 1xxx = comparison

`include "mor1kx-defines.v"

module pfpu32_top
#(
  parameter OPTION_OPERAND_WIDTH = 32
)
(
  input clk,
  input rst,
  input flush_i,
  input padv_decode_i,
  input padv_execute_i,
  input [`OR1K_FPUOP_WIDTH-1:0]    op_fpu_i,
  input [`OR1K_FPCSR_RM_SIZE-1:0]  round_mode_i,
  input [OPTION_OPERAND_WIDTH-1:0] rfa_i,
  input [OPTION_OPERAND_WIDTH-1:0] rfb_i,
  output [OPTION_OPERAND_WIDTH-1:0] fpu_result_o,
  output fpu_valid_o,
  output fpu_cmp_flag_o,
  output fpu_cmp_valid_o,
  output [`OR1K_FPCSR_WIDTH-1:0] fpcsr_o
);

//localparam SNAN = 31'b1111111101111111111111111111111;

// MSB (set by decode stage) indicates FPU instruction
// Get rid of top bit - is FPU op valid bit
wire   is_op_fpu = op_fpu_i[`OR1K_FPUOP_WIDTH-1];
wire [`OR1K_FPUOP_WIDTH-1:0] op_fpu = {1'b0,op_fpu_i[`OR1K_FPUOP_WIDTH-2:0]};
wire [2:0] op_arith = op_fpu_i[2:0]; // alias
wire [2:0] op_conv  = op_fpu_i[2:0]; // alias
wire a_cmp = op_fpu_i[3]; // alias for compare bit of fpu's opcode

// advance FPU units
wire padv_fpu_units = (padv_execute_i & fpu_valid_o) |
                      !fpu_valid_o;

// start logic
reg new_data;
always @(posedge clk `OR_ASYNC_RST) begin
  if (rst)
    new_data <= 0;
  else if(flush_i)
    new_data <= 0;
  else if(padv_decode_i)
    new_data <= 1;
  else if(padv_fpu_units)
    new_data <= 0;
end // posedge clock

wire new_fpu_data = new_data & is_op_fpu;


// analysis of input values
//   split input a
wire        in_signa  = rfa_i[31];
wire [7:0]  in_expa   = rfa_i[30:23];
wire [22:0] in_fracta = rfa_i[22:0];
//   detect infinity a
wire in_expa_ff = &in_expa;
wire in_infa = in_expa_ff & !(|in_fracta);
//   signaling NaN: exponent is 8hff, [22] is zero,
//                  rest of fract is non-zero
//   quiet NaN: exponent is 8hff, [22] is 1
wire in_snan_a = in_expa_ff & !in_fracta[22] & (|in_fracta[21:0]);
wire in_qnan_a = in_expa_ff &  in_fracta[22];
//   denormalized/zero of a
wire in_opa_dn = !(|in_expa) & !in_opa_0;
wire in_opa_0  = !(|rfa_i[30:0]);

//   split input b
wire        in_signb  = rfb_i[31];
wire [7:0]  in_expb   = rfb_i[30:23];
wire [22:0] in_fractb = rfb_i[22:0];
//   detect infinity b
wire in_expb_ff = &in_expb;
wire in_infb  = in_expb_ff & !(|in_fractb);
//   detect NaNs in b
wire in_snan_b = in_expb_ff & !in_fractb[22] & (|in_fractb[21:0]);
wire in_qnan_b = in_expb_ff &  in_fractb[22];
//   denormalized/zero of a
wire in_opb_dn = !(|in_expb) & !in_opb_0;
wire in_opb_0 = !(|rfb_i[30:0]);

// detection of some exceptions
//   a nan input -> qnan output
wire in_snan = in_snan_a | in_snan_b;
wire in_qnan = in_qnan_a | in_qnan_b;
//   sign of output nan
wire in_anan_sign = (in_snan_a | in_qnan_a) ? in_signa :
                                              in_signb;

// restored exponents
wire [9:0] in_exp10a = {2'd0,in_expa} + {9'd0,in_opa_dn};
wire [9:0] in_exp10b = {2'd0,in_expb} + {9'd0,in_opb_dn};
// restored fractionals
wire [23:0] in_fract24a = {(!in_opa_dn & !in_opa_0),in_fracta};
wire [23:0] in_fract24b = {(!in_opb_dn & !in_opb_0),in_fractb};


// addition / substraction
//   inputs & outputs
wire the_sub = (op_arith == 3'd1);
wire op_add = is_op_fpu & (!a_cmp) & ((op_arith == 3'd0) | the_sub);
wire add_start = op_add & new_fpu_data;
wire        add_rdy_o;       // add/sub is ready
wire        add_sign_o;      // add/sub signum
wire  [9:0] add_exp10_o;     // add/sub exponent
wire [23:0] add_fract24_o;   // add/sub fractional
wire  [1:0] add_rs_o;        // add/sub round & sticky bits
wire        add_inv_o;       // add/sub invalid operation flag
wire        add_inf_o;       // add/sub infinity output reg
wire        add_snan_o;      // add/sub signaling NaN output reg
wire        add_qnan_o;      // add/sub quiet NaN output reg
wire        add_anan_sign_o; // add/sub signum for output nan
//   module istance
pfpu32_addsub u_f32_addsub
(
  .clk(clk),
  .rst(rst),
  .flush_i     (flush_i),        // flushe pipe
  .adv_i       (padv_fpu_units), // advance pipe
  .rmode_i     (round_mode_i),   // rounding mode
  .start_i     (add_start), 
  .is_sub_i    (the_sub),        // 1: substruction, 0: addition
  .signa_i     (in_signa),       // input 'a' related values
  .exp10a_i    (in_exp10a),
  .fract24a_i  (in_fract24a),
  .infa_i      (in_infa),
  .signb_i     (in_signb),       // input 'b' related values
  .exp10b_i    (in_exp10b),
  .fract24b_i  (in_fract24b),
  .infb_i      (in_infb),
  .snan_i      (in_snan),        // 'a'/'b' related
  .qnan_i      (in_qnan),
  .anan_sign_i (in_anan_sign),
  .add_rdy_o       (add_rdy_o),       // add/sub is ready
  .add_sign_o      (add_sign_o),      // add/sub signum
  .add_exp10_o     (add_exp10_o),     // add/sub exponent
  .add_fract24_o   (add_fract24_o),   // add/sub fractional
  .add_rs_o        (add_rs_o),        // add/sub round & sticky bits
  .add_inv_o       (add_inv_o),       // add/sub invalid operation flag
  .add_inf_o       (add_inf_o),       // add/sub infinity output reg
  .add_snan_o      (add_snan_o),      // add/sub signaling NaN output reg
  .add_qnan_o      (add_qnan_o),      // add/sub quiet NaN output reg
  .add_anan_sign_o (add_anan_sign_o)  // add/sub signum for output nan
);

// multiplier
//   inputs & outputs
wire op_mul = is_op_fpu & (!a_cmp) & (op_arith == 3'd2);
wire mul_start = op_mul & new_fpu_data;
wire        mul_rdy_o;       // mul is ready
wire        mul_sign_o;      // mul signum
wire  [9:0] mul_exp10_o;     // mul exponent
wire [23:0] mul_fract24_o;   // mul fractional
wire  [1:0] mul_rs_o;        // mul round & sticky bits
wire        mul_inv_o;       // mul invalid operation flag
wire        mul_inf_o;       // mul infinity output reg
wire        mul_snan_o;      // mul signaling NaN output reg
wire        mul_qnan_o;      // mul quiet NaN output reg
wire        mul_anan_sign_o; // mul signum for output nan
//   module istance
pfpu32_mul u_f32_mul
(
  .clk         (clk),
  .rst         (rst),
  .flush_i     (flush_i),        // flushe pipe
  .adv_i       (padv_fpu_units), // advance pipe
  .start_i     (mul_start),
  .signa_i     (in_signa),       // input 'a' related values
  .exp10a_i    (in_exp10a),
  .fract24a_i  (in_fract24a),
  .infa_i      (in_infa),
  .zeroa_i     (in_opa_0),
  .signb_i     (in_signb),       // input 'b' related values
  .exp10b_i    (in_exp10b),
  .fract24b_i  (in_fract24b),
  .infb_i      (in_infb),
  .zerob_i     (in_opb_0),
  .snan_i      (in_snan),        // 'a'/'b' related
  .qnan_i      (in_qnan),
  .anan_sign_i (in_anan_sign),
  .mul_rdy_o       (mul_rdy_o),       // mul is ready
  .mul_sign_o      (mul_sign_o),      // mul signum
  .mul_exp10_o     (mul_exp10_o),     // mul exponent
  .mul_fract24_o   (mul_fract24_o),   // mul fractional
  .mul_rs_o        (mul_rs_o),        // mul round & sticky bits
  .mul_inv_o       (mul_inv_o),       // mul invalid operation flag
  .mul_inf_o       (mul_inf_o),       // mul infinity output reg
  .mul_snan_o      (mul_snan_o),      // mul signaling NaN output reg
  .mul_qnan_o      (mul_qnan_o),      // mul quiet NaN output reg
  .mul_anan_sign_o (mul_anan_sign_o)  // mul signum for output nan
);

// divisor
//   inputs & outputs
wire op_div = is_op_fpu & (!a_cmp) & (op_arith == 3'd3);
wire div_start = op_div & new_fpu_data;
wire        div_rdy_o;       // div is ready
wire        div_sign_o;      // div signum
wire  [9:0] div_exp10_o;     // div exponent
wire [23:0] div_fract24_o;   // div fractional
wire  [1:0] div_rs_o;        // div round & sticky bits
wire        div_inv_o;       // div invalid operation flag
wire        div_inf_o;       // div infinity output reg
wire        div_snan_o;      // div signaling NaN output reg
wire        div_qnan_o;      // div quiet NaN output reg
wire        div_anan_sign_o; // div signum for output nan
wire        div_dbz_o;       // div division by zero flag
wire        div_dbinf_o;     // div division by infinity
//   module istance
pfpu32_div u_f32_div
(
  .clk         (clk),
  .rst         (rst),
  .flush_i     (flush_i),        // flushe pipe
  .adv_i       (padv_fpu_units), // advance pipe
  .start_i     (div_start),
  .signa_i     (in_signa),       // input 'a' related values
  .exp10a_i    (in_exp10a),
  .fract24a_i  (in_fract24a),
  .infa_i      (in_infa),
  .zeroa_i     (in_opa_0),
  .signb_i     (in_signb),       // input 'b' related values
  .exp10b_i    (in_exp10b),
  .fract24b_i  (in_fract24b),
  .infb_i      (in_infb),
  .zerob_i     (in_opb_0),
  .snan_i      (in_snan),        // 'a'/'b' related
  .qnan_i      (in_qnan),
  .anan_sign_i (in_anan_sign),
  .div_rdy_o       (div_rdy_o),       // div is ready
  .div_sign_o      (div_sign_o),      // div signum
  .div_exp10_o     (div_exp10_o),     // div exponent
  .div_fract24_o   (div_fract24_o),   // div fractional
  .div_rs_o        (div_rs_o),        // div round & sticky bits
  .div_inv_o       (div_inv_o),       // div invalid operation flag
  .div_inf_o       (div_inf_o),       // div infinity output reg
  .div_snan_o      (div_snan_o),      // div signaling NaN output reg
  .div_qnan_o      (div_qnan_o),      // div quiet NaN output reg
  .div_anan_sign_o (div_anan_sign_o), // div signum for output nan
  .div_dbz_o       (div_dbz_o),       // div division by zero flag
  .div_dbinf_o     (div_dbinf_o)      // div division by infinity
);

// convertor
//   i2f signals
wire op_i2f_cnv = is_op_fpu & (!a_cmp) &
                  (op_conv == 3'd4);
wire i2f_start = op_i2f_cnv & new_fpu_data;
wire        i2f_rdy_o;       // i2f is ready
wire        i2f_sign_o;      // i2f signum
wire  [9:0] i2f_exp10_o;     // i2f exponent
wire [23:0] i2f_fract24_o;   // i2f fractional
wire  [1:0] i2f_rs_o;        // i2f round & sticky bits
//   i2f module instance
pfpu32_i2f u_i2f_cnv
(
  .clk         (clk),
  .rst         (rst),
  .flush_i     (flush_i),      // flush pipe
  .adv_i       (padv_fpu_units), // advance pipe
  .start_i     (i2f_start),    // start conversion
  .opa_i       (rfa_i),
  .i2f_rdy_o(i2f_rdy_o),       // i2f is ready
  .i2f_sign_o(i2f_sign_o),      // i2f signum
  .i2f_exp10_o(i2f_exp10_o),     // i2f exponent
  .i2f_fract24_o(i2f_fract24_o),   // i2f fractional
  .i2f_rs_o(i2f_rs_o)         // i2f round & sticky bits
);
//   f2i signals
wire op_f2i_cnv = is_op_fpu & (!a_cmp) &
                  (op_conv == 3'd5);
wire f2i_start = op_f2i_cnv & new_fpu_data;
wire        f2i_rdy_o;       // f2i is ready
wire        f2i_sign_o;      // f2i signum
wire [31:0] f2i_int32_o;     // f2i i32 modulo
wire  [1:0] f2i_rs_o;        // f2i round & sticky bits
wire        f2i_ovf_o;       // f2i overflow flag
wire        f2i_snan_o;      // f2i signaling NaN output reg
//    f2i module instance
pfpu32_f2i u_f2i_cnv
(
  .clk         (clk),
  .rst         (rst),
  .flush_i     (flush_i),        // flush pipe
  .adv_i       (padv_fpu_units), // advance pipe
  .start_i     (f2i_start),      // start conversion
  .signa_i     (in_signa),       // input 'a' related values
  .exp10a_i    (in_exp10a),
  .fract24a_i  (in_fract24a),
  .snan_i      (in_snan),        // 'a'/'b' related
  .qnan_i      (in_qnan),
  .f2i_rdy_o   (f2i_rdy_o),       // f2i is ready
  .f2i_sign_o  (f2i_sign_o),      // f2i signum
  .f2i_int32_o (f2i_int32_o),     // f2i i32 modulo
  .f2i_rs_o    (f2i_rs_o),        // f2i round & sticky bits
  .f2i_ovf_o   (f2i_ovf_o),       // f2i overflow flag
  .f2i_snan_o  (f2i_snan_o)       // f2i signaling NaN output reg
);

// comparator
//   inputs & outputs
wire op_cmp = is_op_fpu & a_cmp &
              new_fpu_data;
wire cmp_result, cmp_ready,
     cmp_inv, cmp_inf;
//   module istance
pfpu32_fcmp u_f32_cmp
(
  .fpu_op_is_comp_i(op_cmp),
  .cmp_type_i(op_fpu),
  .opa_i(rfa_i),
  .opb_i(rfb_i),
  .cmp_flag_o(cmp_result),
  .inv_o(cmp_inv),
  .inf_o(cmp_inf),
  .ready_o(cmp_ready)
);


// multiplexing and rounding
pfpu32_rnd u_f32_rnd
(
  // clocks, resets and other controls
  .clk             (clk),
  .rst             (rst),
  .flush_i         (flush_i),         // flush pipe
  .adv_i           (padv_fpu_units),  // advance pipe
  .rmode_i         (round_mode_i),    // rounding mode
  // from add/sub
  .add_rdy_i       (add_rdy_o),       // add/sub is ready
  .add_sign_i      (add_sign_o),      // add/sub signum
  .add_exp10_i     (add_exp10_o),     // add/sub exponent
  .add_fract24_i   (add_fract24_o),   // add/sub fractional
  .add_rs_i        (add_rs_o),        // add/sub round & sticky bits
  .add_inv_i       (add_inv_o),       // add/sub invalid operation flag
  .add_inf_i       (add_inf_o),       // add/sub infinity
  .add_snan_i      (add_snan_o),      // add/sub signaling NaN
  .add_qnan_i      (add_qnan_o),      // add/sub quiet NaN
  .add_anan_sign_i (add_anan_sign_o), // add/sub signum for output nan
  // . from mul
  .mul_rdy_i       (mul_rdy_o),       // mul is ready
  .mul_sign_i      (mul_sign_o),      // mul signum
  .mul_exp10_i     (mul_exp10_o),     // mul exponent
  .mul_fract24_i   (mul_fract24_o),   // mul fractional
  .mul_rs_i        (mul_rs_o),        // mul round & sticky bits
  .mul_inv_i       (mul_inv_o),       // mul invalid operation flag
  .mul_inf_i       (mul_inf_o),       // mul infinity 
  .mul_snan_i      (mul_snan_o),      // mul signaling NaN
  .mul_qnan_i      (mul_qnan_o),      // mul quiet NaN
  .mul_anan_sign_i (mul_anan_sign_o), // mul signum for output nan
  // . from div
  .div_rdy_i       (div_rdy_o),       // div is ready
  .div_sign_i      (div_sign_o),      // div signum
  .div_exp10_i     (div_exp10_o),     // div exponent
  .div_fract24_i   (div_fract24_o),   // div fractional
  .div_rs_i        (div_rs_o),        // div round & sticky bits
  .div_inv_i       (div_inv_o),       // div invalid operation flag
  .div_inf_i       (div_inf_o),       // div infinity 
  .div_snan_i      (div_snan_o),      // div signaling NaN
  .div_qnan_i      (div_qnan_o),      // div quiet NaN 
  .div_anan_sign_i (div_anan_sign_o), // div signum for output nan
  .div_dbz_i       (div_dbz_o),       // div division by zero flag
  .div_dbinf_i     (div_dbinf_o),     // div division by infinity
  // . from i2f
  .i2f_rdy_i       (i2f_rdy_o),       // i2f is ready
  .i2f_sign_i      (i2f_sign_o),      // i2f signum
  .i2f_exp10_i     (i2f_exp10_o),     // i2f exponent
  .i2f_fract24_i   (i2f_fract24_o),   // i2f fractional
  .i2f_rs_i        (i2f_rs_o),        // i2f round & sticky bits
  // . from f2i
  .f2i_rdy_i       (f2i_rdy_o),       // f2i is ready
  .f2i_sign_i      (f2i_sign_o),      // f2i signum
  .f2i_int32_i     (f2i_int32_o),     // f2i i32 modulo
  .f2i_rs_i        (f2i_rs_o),        // f2i round & sticky bits
  .f2i_ovf_i       (f2i_ovf_o),       // f2i overflow flag
  .f2i_snan_i      (f2i_snan_o),      // f2i signaling NaN
   // . from cmp
  .cmp_rdy_i       (cmp_ready),       // cmp is ready
  .cmp_res_i       (cmp_result),      // cmp result
  .cmp_inv_i       (cmp_inv),         // cmp invalid flag
  .cmp_inf_i       (cmp_inf),         // cmp infinity flag
  // outputs
  .fpu_result_o    (fpu_result_o),
  .fpu_valid_o     (fpu_valid_o),
  .fpu_cmp_flag_o  (fpu_cmp_flag_o),
  .fpu_cmp_valid_o (fpu_cmp_valid_o),
  .fpcsr_o         (fpcsr_o)
);

endmodule // pfpu32_top
