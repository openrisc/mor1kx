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
  output reg [OPTION_OPERAND_WIDTH-1:0] fpu_result_o,
  output reg fpu_valid_o,
  output reg fpu_cmp_flag_o,
  output reg fpu_cmp_valid_o,
  output reg [`OR1K_FPCSR_WIDTH-1:0] fpcsr_o
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
  if (rst | flush_i)
    new_data <= 0;
  else if(padv_decode_i)
    new_data <= 1;
  else if(padv_fpu_units)
    new_data <= 0;
end // posedge clock

wire new_fpu_data = new_data & is_op_fpu;


// addition / substraction
//   inputs & outputs
wire the_sub = (op_arith == 3'd1);
wire op_add = is_op_fpu & (!a_cmp) & ((op_arith == 3'd0) | the_sub);
wire add_start = op_add & new_fpu_data;
wire add_ine, add_inv, add_ovf, add_inf, add_unf, add_zero;
wire [OPTION_OPERAND_WIDTH-1:0] add_result;
wire add_ready;
//   module istance
pfpu32_addsub u_f32_addsub
(
  .clk(clk),
  .rst(rst),
  .flush_i(flush_i),  // flushe pipe
  .adv_i(padv_fpu_units),    // advance pipe
  .start_i(add_start), 
  .is_sub_i(the_sub), // 1: substruction, 0: addition
  .rmode_i(round_mode_i),  // round mode
  .opa_i(rfa_i),
  .opb_i(rfb_i),
  .opc_o(add_result),
  .ine_o(add_ine),
  .inv_o(add_inv),  // inf-inf -> invalid flag & qnan result
  .ovf_o(add_ovf),
  .inf_o(add_inf),
  .unf_o(add_unf),
  .zer_o(add_zero),
  .ready_o(add_ready)
);

// multiplier
//   inputs & outputs
wire op_mul = is_op_fpu & (!a_cmp) & (op_arith == 3'd2);
wire mul_start = op_mul & new_fpu_data;
wire mul_ine, mul_inv, mul_ovf, mul_inf, mul_unf, mul_zero;
wire [OPTION_OPERAND_WIDTH-1:0] mul_result;
wire mul_ready;
//   module istance
pfpu32_mul u_f32_mul
(
  .clk(clk),
  .rst(rst),
  .flush_i(flush_i),  // flushe pipe
  .adv_i(padv_fpu_units),    // advance pipe
  .start_i(mul_start),
  .rmode_i(round_mode_i),  // round mode
  .opa_i(rfa_i),
  .opb_i(rfb_i),
  .opc_o(mul_result),
  .ine_o(mul_ine),
  .inv_o(mul_inv),
  .ovf_o(mul_ovf),
  .inf_o(mul_inf),
  .unf_o(mul_unf),
  .zer_o(mul_zero),
  .ready_o(mul_ready)
);

// divisor
//   inputs & outputs
wire op_div = is_op_fpu & (!a_cmp) & (op_arith == 3'd3);
wire div_start = op_div & new_fpu_data;
wire div_ine, div_inv, div_ovf, div_inf, div_unf, div_zero, div_dbz;
wire [OPTION_OPERAND_WIDTH-1:0] div_result;
wire div_ready;
//   module istance
pfpu32_div u_f32_div
(
  .clk(clk),
  .rst(rst),
  .flush_i(flush_i),  // flushe pipe
  .adv_i(padv_fpu_units),    // advance pipe
  .start_i(div_start),
  .rmode_i(round_mode_i),  // round mode
  .opa_i(rfa_i),
  .opb_i(rfb_i),
  .opc_o(div_result),
  .ine_o(div_ine),
  .inv_o(div_inv), // 0/0, inf/inf -> invalid flag & qnan result
  .ovf_o(div_ovf),
  .inf_o(div_inf),
  .unf_o(div_unf),
  .zer_o(div_zero),
  .dbz_o(div_dbz),    // division by zero
  .ready_o(div_ready)
);

// convertor
//   i2f signals
wire op_i2f_cnv = is_op_fpu & (!a_cmp) &
                  (op_conv == 3'd4);
wire i2f_start = op_i2f_cnv & new_fpu_data;
wire [OPTION_OPERAND_WIDTH-1:0] i2f_result;
wire i2f_ine, i2f_zero;
wire i2f_ready;
//   i2f module instance
pfpu32_i2f u_i2f_cnv
(
  .clk(clk),
  .rst(rst),
  .rmode_i(round_mode_i),
  .opa_i(rfa_i),
  .flush_i(flush_i),      // flush pipe
  .adv_i(padv_fpu_units), // advance pipe
  .start_i(i2f_start),    // start conversion
  .opc_o(i2f_result),
  .ine_o(i2f_ine),
  .zer_o(i2f_zero),
  .ready_o(i2f_ready)
);
//   f2i signals
wire op_f2i_cnv = is_op_fpu & (!a_cmp) &
                  (op_conv == 3'd5);
wire f2i_start = op_f2i_cnv & new_fpu_data;
wire [OPTION_OPERAND_WIDTH-1:0] f2i_result;
wire f2i_ine, f2i_inv, f2i_unf, f2i_zero, f2i_snan;
wire f2i_ready;
//    f2i module instance
pfpu32_f2i u_f2i_cnv
(
  .clk(clk),
  .rst(rst),
  .rmode_i(round_mode_i),
  .opa_i(rfa_i),
  .flush_i(flush_i),      // flush pipe
  .adv_i(padv_fpu_units), // advance pipe
  .start_i(f2i_start),    // start conversion
  .out_o(f2i_result),
  .nan_o(f2i_snan),
  .ine_o(f2i_ine),
  .inv_o(f2i_inv),
  .unf_o(f2i_unf),
  .zer_o(f2i_zero),
  .ready_o(f2i_ready)
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


// arithmetic units outputs mux
wire [OPTION_OPERAND_WIDTH-1:0] fpu_result;
assign fpu_result = add_ready ? add_result :
                    mul_ready ? mul_result :
                    div_ready ? div_result :
                    i2f_ready ? i2f_result :
                    f2i_ready ? f2i_result :
                    {OPTION_OPERAND_WIDTH{1'b0}};

// Prepare exeptions
wire exp_result_ff = &fpu_result[30:23];
wire qnan_result   = exp_result_ff & fpu_result[22];
wire snan_result   = exp_result_ff & !fpu_result[22] & (|fpu_result[21:0]);

wire arith_ready = add_ready | mul_ready | div_ready;

// Output register
always @(posedge clk `OR_ASYNC_RST) begin
  if (rst | flush_i) begin
      // overall FPU results
    fpu_result_o    <= {OPTION_OPERAND_WIDTH{1'b0}};
    fpu_valid_o     <= 1'b0;
      // comparison specials
    fpu_cmp_flag_o  <= 1'b0;
    fpu_cmp_valid_o <= 1'b0;
      // exeptions
    fpcsr_o         <= {`OR1K_FPCSR_WIDTH{1'b0}};
  end
  else if(padv_fpu_units) begin
      // overall FPU results
    fpu_result_o    <= fpu_result;
    fpu_valid_o     <= arith_ready | i2f_ready | 
                         f2i_ready | cmp_ready;
      // comparison specials
    fpu_cmp_flag_o  <= cmp_result;
    fpu_cmp_valid_o <= cmp_ready;
      // exeptions
    fpcsr_o[`OR1K_FPCSR_OVF] <= (add_ready & add_ovf) |
                                (mul_ready & mul_ovf) |
                                (div_ready & div_ovf);
    fpcsr_o[`OR1K_FPCSR_UNF] <= (add_ready & add_unf) |
                                (mul_ready & mul_unf) |
                                (div_ready & div_unf) |
                                (f2i_ready & f2i_unf);
    fpcsr_o[`OR1K_FPCSR_SNF] <= (arith_ready & snan_result)|
                                (f2i_ready & f2i_snan);
    fpcsr_o[`OR1K_FPCSR_QNF] <= (arith_ready & qnan_result);
    fpcsr_o[`OR1K_FPCSR_ZF]  <= (add_ready & add_zero) |
                                (mul_ready & mul_zero) |
                                (div_ready & div_zero) |
                                (i2f_ready & i2f_zero) |
                                (f2i_ready & f2i_zero);
    fpcsr_o[`OR1K_FPCSR_IXF] <= (add_ready & add_ine) |
                                (mul_ready & mul_ine) |
                                (div_ready & div_ine) |
                                (i2f_ready & i2f_ine) |
                                (f2i_ready & f2i_ine);
    fpcsr_o[`OR1K_FPCSR_IVF] <= (add_ready & add_inv) |
                                (mul_ready & mul_inv) |  
                                (div_ready & div_inv) |
                                (f2i_ready & (f2i_inv | f2i_snan)) |
                                (cmp_ready & cmp_inv);
    fpcsr_o[`OR1K_FPCSR_INF] <= (add_ready & add_inf) |
                                (mul_ready & mul_inf) |
                                (div_ready & div_inf) |
                                (cmp_ready & cmp_inf);
    fpcsr_o[`OR1K_FPCSR_DZF] <= (div_ready & div_dbz);
  end
end // posedge clock

endmodule // pfpu32_top
