/////////////////////////////////////////////////////////////////////
////                                                             ////
////  mor1kx_fpu_intfloat_conv                                   ////
////  Only conversion between 32-bit integer and single          ////
////  precision floating point format                            ////
////                                                             ////
////  Author: Rudolf Usselmann                                   ////
////          rudi@asics.ws                                      ////
////                                                             ////
//// Modified by Julius Baxter, July, 2010                       ////
////             julius.baxter@orsoc.se                          ////
////                                                             ////
//// Update for mor1kx, bug fixing and further development       ////
////             Andrey Bacherov, 2014,                          ////
////             avbacherov@opencores.org                        ////
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

/*

 FPU Operations (fpu_op):
 ========================

 0 =
 1 =
 2 =
 3 =
 4 = int to float
 5 = float to int
 6 =
 7 =

 Rounding Modes (rmode):
 =======================

 0 = round_nearest_even
 1 = round_to_zero
 2 = round_up
 3 = round_down

 */


module mor1kx_fpu_intfloat_conv
#(
   parameter  INF  = 31'h7f800000,
              QNAN = 31'h7fc00001,
              SNAN = 31'h7f800001
)
(
   input         clk,
   input         rst,
   input [1:0]   rmode,
   input [2:0]   fpu_op,
   input [31:0]  opa,
   input         clr_ready_flag_i,
   input         start_i,
   output [31:0] out,
   output        ready_o,
   output        snan,
   output        ine,
   output        inv,
   output        overflow,
   output        underflow,
   output        zero
);

   ////////////////////////////////////////////////////////////////////////
   //
   // Local Wires
   //
   reg      zero;
   reg [31:0]     opa_r;  // Input operand registers
   reg [31:0]     out;    // Output register
   reg      div_by_zero;  // Divide by zero output register
   wire [7:0]     exp_fasu; // Exponent output from EQU block
   reg [7:0]    exp_r;    // Exponent output (registerd)
   wire     co;   // carry output
   wire [30:0]    out_d;    // Intermediate final result output
   wire     overflow_d, underflow_d;// Overflow/Underflow
   reg      inf, snan, qnan;// Output Registers for INF, S/QNAN
   reg      ine;    // Output Registers for INE
   reg [1:0]    rmode_r1, rmode_r2,// Pipeline registers for round mode
      rmode_r3;
   reg [2:0]    fpu_op_r1, fpu_op_r2,// Pipeline registers for fp
                           // operation
      fpu_op_r3;

   ////////////////////////////////////////////////////////////////////////
   //
   // Input Registers
   //
   always @(posedge clk `OR_ASYNC_RST)
   if (rst) begin
     opa_r <=  32'd0;
     rmode_r1 <=  2'd0;
     rmode_r2 <=  2'd0;
     rmode_r3 <=  2'd0;
     fpu_op_r1 <=  3'd0;
     fpu_op_r2 <=  3'd0;
     fpu_op_r3 <=  3'd0;
   end
   else begin
     opa_r <=  opa;
     rmode_r1 <=  rmode;
     rmode_r2 <=  rmode_r1;
     rmode_r3 <=  rmode_r2;
     fpu_op_r1 <=  fpu_op;
     fpu_op_r2 <=  fpu_op_r1;
     fpu_op_r3 <=  fpu_op_r2;
   end

   ////////////////////////////////////////////////////////////////////////
   //
   // Ready flag generation
   // 5-long shift reg for conversion ready counter
   // we don't reset ready flag till next fpu instruction
   // but it is blocked by combination of 'is_op_fpu' and 'decode_valid_o'
   // on upper level
   parameter t_state_waiting = 0,
            t_state_busy    = 1;
   reg     s_state;
   reg [6:0] fpu_conv_shr;
   always @(posedge clk `OR_ASYNC_RST) begin
     if (rst) begin
       fpu_conv_shr <= 7'd0;
       s_state <= t_state_waiting;
     end
     else if(start_i) begin
       fpu_conv_shr <= 7'd1;
       s_state <= t_state_busy;
     end
     else if(clr_ready_flag_i) begin
       fpu_conv_shr <= 7'd0;
       s_state <= t_state_waiting;
     end
     else if(s_state == t_state_busy) begin
       if(!ready_o) begin
         fpu_conv_shr <= {fpu_conv_shr[5:0],1'b1};
         s_state <= s_state;
       end
       else begin
         fpu_conv_shr <= fpu_conv_shr;
         s_state <= t_state_waiting;
       end
     end
     else begin
       fpu_conv_shr <= fpu_conv_shr;
       s_state <= s_state;
     end
   end // posedge clock

   assign ready_o = fpu_conv_shr[6];

   ////////////////////////////////////////////////////////////////////////
   //
   // Exceptions block
   //
   wire     inf_d, ind_d, qnan_d, snan_d, opa_nan;
   wire     opa_00;
   wire     opa_inf;

   mor1kx_fpu_intfloat_conv_except u0
     (  .clk(clk),
  .rst(rst),
  .opa(opa_r),
  .opb(),
  .inf(inf_d),
  .ind(ind_d),
  .qnan(qnan_d),
  .snan(snan_d),
  .opa_nan(opa_nan),
  .opb_nan(),
  .opa_00(opa_00),
  .opb_00(),
  .opa_inf(opa_inf),
  .opb_inf()
  );

   ////////////////////////////////////////////////////////////////////////
   //
   // Pre-Normalize block
   // - Adjusts the numbers to equal exponents and sorts them
   // - determine result sign
   // - determine actual operation to perform (add or sub)
   //

   wire     nan_sign_d, result_zero_sign_d;
   reg      sign_fasu_r;
   wire [1:0]     exp_ovf;
   reg [1:0]    exp_ovf_r;

   // This is all we need from post-norm module for int-float conversion
   reg      opa_sign_r;
   always @(posedge clk `OR_ASYNC_RST)
   if (rst) begin
     opa_sign_r <= 0;
     sign_fasu_r <=  0; //sign_fasu;
   end
   else begin
     opa_sign_r <= opa_r[31];
     sign_fasu_r <=  opa_sign_r; //sign_fasu;
   end


   ////////////////////////////////////////////////////////////////////////
   //
   // Normalize Result
   //
   wire     ine_d;
   wire     inv_d;
   wire     sign_d;
   reg      sign;
   reg [30:0]     opa_r1;
   reg [47:0]     fract_i2f;
   reg      opas_r1, opas_r2;
   wire     f2i_out_sign;
   wire [47:0]    fract_denorm;

   // Exponent must be once cycle delayed
   always @(posedge clk `OR_ASYNC_RST)
   if (rst)
     exp_r <= 0;
   else begin
     case(fpu_op_r2)
       5: exp_r <=  opa_r1[30:23];
       default: exp_r <=  0;
     endcase
   end

   always @(posedge clk `OR_ASYNC_RST)
   if (rst)
     opa_r1 <=  0;
   else
     opa_r1 <=  opa_r[30:0];

   always @(posedge clk `OR_ASYNC_RST)
   if (rst)
     fract_i2f <= 0;
   else
     fract_i2f <=  (fpu_op_r2==5) ?
       (sign_d ?  1-{24'h00, (|opa_r1[30:23]), opa_r1[22:0]}-1 :
        {24'h0, (|opa_r1[30:23]), opa_r1[22:0]})
       : (sign_d ? 1 - {opa_r1, 17'h01} : {opa_r1, 17'h0});

   assign fract_denorm = fract_i2f;

   always @(posedge clk `OR_ASYNC_RST)
   if (rst)
     opas_r1 <=  0;
   else
     opas_r1 <=  opa_r[31];

   always @(posedge clk `OR_ASYNC_RST)
   if (rst)
     opas_r2 <=  0;
   else
     opas_r2 <=  opas_r1;

   assign sign_d = opa_sign_r; //sign_fasu;


   always @(posedge clk `OR_ASYNC_RST)
   if (rst)
     sign <=  0;
   else
     sign <=  (rmode_r2==2'h3) ? !sign_d : sign_d;


   // Special case of largest negative integer we can convert to - usually
   // gets picked up as invalid, but really it's not, so deal with it as a
   // special case.
   wire     f2i_special_case_no_inv;
   assign f2i_special_case_no_inv = (opa == 32'hcf000000);


   mor1kx_fpu_post_norm_intfloat_conv u4
     (
      .clk(clk),      // System Clock
      .rst(rst),
      .fpu_op(fpu_op_r3),   // Floating Point Operation
      .opas(opas_r2),     // OPA Sign
      .sign(sign),      // Sign of the result
      .rmode(rmode_r3),   // Rounding mode
      .fract_in(fract_denorm),  // Fraction Input

      .exp_in(exp_r),     // Exponent Input
      .opa_nan(opa_nan),
      .opa_inf(opa_inf),

      .out(out_d),    // Normalized output (un-registered)
      .ine(ine_d),    // Result Inexact output (un-registered)
      .inv(inv_d),            // Invalid input for f2i operation
      .overflow(overflow_d),  // Overflow output (un-registered)
      .underflow(underflow_d),// Underflow output (un-registered)
      .f2i_out_sign(f2i_out_sign) // F2I Output Sign
      );

   ////////////////////////////////////////////////////////////////////////
     //
   // FPU Outputs
   //
   reg      fasu_op_r1, fasu_op_r2;
   wire [30:0]    out_fixed;
   wire     output_zero_fasu;
   wire     overflow_fasu;
   wire     out_d_00;
   wire     ine_fasu;
   wire     underflow_fasu;

   // Force pre-set values for non numerical output
   assign out_fixed = (qnan_d | snan_d | ind_d)  ? QNAN : INF;

   always @(posedge clk `OR_ASYNC_RST)
   if (rst)
     out[30:0] <=  0;
   else
     out[30:0] <=  out_d;

   assign out_d_00 = !(|out_d);

   always @(posedge clk `OR_ASYNC_RST)
   if (rst)
     out[31] <= 0;
   else
     out[31] <= (fpu_op_r3==3'b101) ?  f2i_out_sign : sign_fasu_r;

   // Exception Outputs
   assign ine_fasu = (ine_d | overflow_d | underflow_d) &
         !(snan_d | qnan_d | inf_d);

   always @(posedge clk `OR_ASYNC_RST)
   if (rst)
     ine <=    0;
   else
     ine <=    fpu_op_r3[2] ? ine_d : ine_fasu;

   assign overflow = overflow_d & !(snan_d | qnan_d | inf_d);
   assign underflow = underflow_d & !(inf_d | snan_d | qnan_d);

   always @(posedge clk `OR_ASYNC_RST)
   if (rst)
     snan <=  0;
   else
     snan <=  snan_d & (fpu_op_r3==3'b101);  // Only signal sNaN when ftoi

   // Status Outputs
   assign output_zero_fasu = out_d_00 & !(inf_d | snan_d | qnan_d);

   always @(posedge clk `OR_ASYNC_RST)
   if (rst)
     zero <= 0;
   else
     zero <=  (fpu_op_r3==3'b101) ? (out_d_00 & !(snan_d | qnan_d)) :
       output_zero_fasu ;

   assign inv = inv_d & !f2i_special_case_no_inv;

endmodule // mor1kx_fpu_intfloat_conv
