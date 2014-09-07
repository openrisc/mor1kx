//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200 FPU arith                                            ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://opencores.org/project,or1k                           ////
////                                                              ////
////  Description                                                 ////
////  Wrapper for floating point arithmetic units.                ////
////                                                              ////
////  To Do:                                                      ////
////   - lf.rem.s and lf.madd.s instruction support               ////
////                                                              ////
////  Author(s):                                                  ////
////      - Original design (FPU100) -                            ////
////        Jidan Al-eryani, jidan@gmx.net                        ////
////      - Conv. to Verilog and inclusion in OR1200 -            ////
////        Julius Baxter, julius@opencores.org                   ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
//
//  Copyright (C) 2006, 2010
//
//  This source file may be used and distributed without
//  restriction provided that this copyright statement is not
//  removed from the file and that any derivative work contains
//  the original copyright notice and the associated disclaimer.
//
//    THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY
//  EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
//  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
//  FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL THE AUTHOR
//  OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
//  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
//  (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
//  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
//  BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
//  LIABILITY, WHETHER IN  CONTRACT, STRICT LIABILITY, OR TORT
//  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
//  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
//  POSSIBILITY OF SUCH DAMAGE.
//

module mor1kx_fpu_arith
  (
   clk,
   opa_i,
   opb_i,
   fpu_op_i,
   rmode_i,
   output_o,
   clr_ready_flag_i,
   start_i,
   ready_o,
   ine_o,
   overflow_o,
   underflow_o,
   div_zero_o,
   inf_o,
   zero_o,
   qnan_o,
   snan_o
   );

   parameter FP_WIDTH = 32;
   //parameter MUL_SERIAL = 1; // 0 for parallel multiplier, 1 for serial
   parameter MUL_COUNT = 34; //11 for parallel multiplier, 34 for serial
   parameter FRAC_WIDTH = 23;
   parameter EXP_WIDTH = 8;
   parameter ZERO_VECTOR = 31'd0;
   parameter INF = 31'b1111111100000000000000000000000;
   parameter QNAN = 31'b11111111_10000000000000000000000;
   parameter SNAN = 31'b11111111_00000000000000000000001;

   // fpu operations (fpu_op_i):
   // ========================
   // 000 = add,
   // 001 = substract,
   // 010 = multiply,
   // 011 = divide,
   // 100 = square root - DISABLED - JPB
   // 101 = unused
   // 110 = unused
   // 111 = unused

   // Rounding Mode:
   // ==============
   // 00 = round to nearest even (default),
   // 01 = round to zero,
   // 10 = round up,
   // 11 = round down

   input  clk;
   input [FP_WIDTH-1:0]      opa_i;
   input [FP_WIDTH-1:0]      opb_i;
   input [2:0]         fpu_op_i;
   input [1:0]         rmode_i;
   input                     clr_ready_flag_i;
   input         start_i;
   output reg          ready_o;
   output reg [FP_WIDTH-1:0] output_o;
   output reg          ine_o;
   output reg          overflow_o;
   output reg          underflow_o;
   output reg          div_zero_o;
   output reg          inf_o;
   output reg          zero_o;
   output reg          qnan_o;
   output reg          snan_o;


   parameter                 t_state_waiting = 0,
                       t_state_busy    = 1;
   reg           s_state;
   reg                       serial_start;
   reg [5:0]         s_count; // Max value of 64

   reg [FP_WIDTH-1:0]        opa_r;
   reg [FP_WIDTH-1:0]        opb_r;

   reg [FP_WIDTH-1:0]        s_output1;
   reg [FP_WIDTH-1:0]        s_output_o; // Comb

   reg           s_ine_o;

   wire          s_overflow_o,
           s_underflow_o,
           s_div_zero_o,
           s_inf_o, s_zero_o, s_qnan_o, s_snan_o;

   wire          s_infa, s_infb;

   //// ***Add/Substract units signals***
   wire [27:0]         prenorm_addsub_fracta_28_o;
   wire [27:0]         prenorm_addsub_fractb_28_o;

   wire [7:0]          prenorm_addsub_exp_o;

   wire [27:0]         addsub_fract_o;
   wire          addsub_sign_o;

   wire [31:0]         postnorm_addsub_output_o;
   wire          postnorm_addsub_ine_o;

   //// ***Multiply units signals***

   wire [9:0]          pre_norm_mul_exp_10;
   wire [23:0]         pre_norm_mul_fracta_24 ;
   wire [23:0]         pre_norm_mul_fractb_24 ;
   wire [47:0]         mul_fract_48;
   //wire [47:0]         mul_24_fract_48;
   //wire          mul_24_sign;
   wire [47:0]         serial_mul_fract_48;
   wire          serial_mul_sign;
   wire          mul_sign;
   wire [31:0]         post_norm_mul_output   ;
   wire          post_norm_mul_ine;


   //// ***Division units signals***

   wire [49:0]         pre_norm_div_dvdnd;
   wire [26:0]         pre_norm_div_dvsor;
   wire [EXP_WIDTH+1:0]      pre_norm_div_exp;
   wire [26:0]         serial_div_qutnt;
   wire [26:0]         serial_div_rmndr;
   wire          serial_div_sign;
   wire          serial_div_div_zero;
   wire [31:0]         post_norm_div_output;
   wire          post_norm_div_ine;


   //// ***Square units***

   wire [51:0]         pre_norm_sqrt_fracta_o;
   wire [7:0]          pre_norm_sqrt_exp_o;
   wire [25:0]         sqrt_sqr_o;
   wire          sqrt_ine_o;

   wire [31:0]         post_norm_sqrt_output  ;
   wire          post_norm_sqrt_ine_o;


   //////////////////////////////////////////////////////////////////-
   // latch input
   always @(posedge clk) begin
     if(start_i) begin
       opa_r <= opa_i;
       opb_r <= opb_i;
     end
   end // @ckl


   //////////////////////////////////////////////////////////////////-
   // generate start flag for serial divider and multiplier
   always @(posedge clk)
     serial_start <= start_i;


   //////////////////////////////////////////////////////////////////-
   // ready flag generator
   // we don't reset ready flag till next fpu instruction
   // but it is blocked by combination of 'is_op_fpu' and 'decode_valid_o'
   // on upper level
   always @(posedge clk)
     begin
       if (clr_ready_flag_i) begin
   ready_o <= 0;
   s_count <= s_count;
   s_state <= t_state_waiting;
       end
       else if (serial_start) begin
   ready_o <= ready_o;
   s_count <= 0;
   s_state <= t_state_busy;
       end
       else if (s_state == t_state_busy) begin
   // Ready cases
   if (((s_count == 6) & ((fpu_op_i==3'd0) | (fpu_op_i==3'd1))) |
       ((s_count==MUL_COUNT) & (fpu_op_i==3'd2)) |
       ((s_count==33) & (fpu_op_i==3'd3))) begin
     ready_o <= 1;
     s_count <= s_count;
     s_state <= t_state_waiting;
   end
   else begin
     ready_o <= ready_o;
     s_count <= s_count + 1;
     s_state <= s_state;
   end
       end // busy
       else begin
   ready_o <= ready_o;
   s_count <= s_count;
   s_state <= s_state;
       end // not ready yet / ready
     end // posedge clock

   //***Add/Substract units***
   mor1kx_fpu_pre_norm_addsub fpu_prenorm_addsub
   (
      .clk(clk),
      .opa_i(opa_r),
      .opb_i(opb_r),
      .fracta_28_o(prenorm_addsub_fracta_28_o),
      .fractb_28_o(prenorm_addsub_fractb_28_o),
      .exp_o(prenorm_addsub_exp_o) );

   mor1kx_fpu_addsub fpu_addsub
     (
      .clk(clk),
      .fpu_op_i(fpu_op_i[0]),
      .fracta_i(prenorm_addsub_fracta_28_o),
      .fractb_i(prenorm_addsub_fractb_28_o),
      .signa_i( opa_r[31]),
      .signb_i( opb_r[31]),
      .fract_o(addsub_fract_o),
      .sign_o(addsub_sign_o)  );

   mor1kx_fpu_post_norm_addsub fpu_postnorm_addsub
     (
      .clk(clk),
      .opa_i(opa_r),
      .opb_i(opb_r),
      .fract_28_i(addsub_fract_o),
      .exp_i(prenorm_addsub_exp_o),
      .sign_i(addsub_sign_o),
      .fpu_op_i(fpu_op_i[0]),
      .rmode_i(rmode_i),
      .output_o(postnorm_addsub_output_o),
      .ine_o(postnorm_addsub_ine_o)
      );

   //***Multiply units***

   mor1kx_fpu_pre_norm_mul fpu_pre_norm_mul
     (
      .clk(clk),
      .opa_i(opa_r),
      .opb_i(opb_r),
      .exp_10_o(pre_norm_mul_exp_10),
      .fracta_24_o(pre_norm_mul_fracta_24),
      .fractb_24_o(pre_norm_mul_fractb_24));
   /*
    mul_24 i_mul_24
    (
    .clk(clk),
    .fracta_i(pre_norm_mul_fracta_24),
    .fractb_i(pre_norm_mul_fractb_24),
    .signa_i(opa_r[31]),
    .signb_i(opb_r[31]),
    .start_i(serial_start),
    .fract_o(mul_24_fract_48),
    .sign_o(mul_24_sign),
    .ready_o()  );
    */
   // Serial multiply is default and only one included here
   mor1kx_fpu_mul fpu_mul
     (
      .clk(clk),
      .fracta_i(pre_norm_mul_fracta_24),
      .fractb_i(pre_norm_mul_fractb_24),
      .signa_i(opa_r[31]),
      .signb_i(opb_r[31]),
      .start_i(serial_start),
      .fract_o(serial_mul_fract_48),
      .sign_o(serial_mul_sign),
      .ready_o()
      );

   // Serial or parallel multiplier will be chosen depending on constant
   //assign mul_fract_48 = MUL_SERIAL ? serial_mul_fract_48 : mul_24_fract_48;
   //assign mul_sign = MUL_SERIAL ? serial_mul_sign : mul_24_sign;
   assign mul_fract_48 = serial_mul_fract_48;
   assign mul_sign = serial_mul_sign;

   mor1kx_fpu_post_norm_mul fpu_post_norm_mul
     (
      .clk(clk),
      .opa_i(opa_r),
      .opb_i(opb_r),
      .exp_10_i(pre_norm_mul_exp_10),
      .fract_48_i(mul_fract_48), // Parallel multiplier input
      .sign_i(mul_sign), // Parallel multiplier input
      .rmode_i(rmode_i),
      .output_o(post_norm_mul_output),
      .ine_o(post_norm_mul_ine)
      );

   ////***Division units***

   mor1kx_fpu_pre_norm_div fpu_pre_norm_div
     (
      .clk(clk),
      .opa_i(opa_r),
      .opb_i(opb_r),
      .exp_10_o(pre_norm_div_exp),
      .dvdnd_50_o(pre_norm_div_dvdnd),
      .dvsor_27_o(pre_norm_div_dvsor)  );

   mor1kx_fpu_div fpu_div
     (
      .clk(clk),
      .dvdnd_i(pre_norm_div_dvdnd),
      .dvsor_i(pre_norm_div_dvsor),
      .sign_dvd_i(opa_r[31]),
      .sign_div_i(opb_r[31]),
      .start_i(serial_start),
      .ready_o(),
      .qutnt_o(serial_div_qutnt),
      .rmndr_o(serial_div_rmndr),
      .sign_o(serial_div_sign),
      .div_zero_o(serial_div_div_zero)   );

   mor1kx_fpu_post_norm_div fpu_post_norm_div
     (
      .clk(clk),
      .opa_i(opa_r),
      .opb_i(opb_r),
      .qutnt_i(serial_div_qutnt),
      .rmndr_i(serial_div_rmndr),
      .exp_10_i(pre_norm_div_exp),
      .sign_i(serial_div_sign),
      .rmode_i(rmode_i),
      .output_o(post_norm_div_output),
      .ine_o(post_norm_div_ine)  );


   //////////////////////////////////////////////////////////////////-
   // Output registers
   always @(posedge clk)
     begin
  output_o <= s_output_o;
  ine_o <= s_ine_o;
  overflow_o <= s_overflow_o;
  underflow_o <= s_underflow_o;
  div_zero_o <= s_div_zero_o & !s_infa;
  inf_o <= s_inf_o;
  zero_o <= s_zero_o;
  qnan_o <= s_qnan_o;
  snan_o <= s_snan_o;
     end

   //// Output Multiplexer
   always @(posedge clk)
     begin
  case(fpu_op_i)
    3'd0,
      3'd1: begin
         s_output1 <= postnorm_addsub_output_o;
         s_ine_o <= postnorm_addsub_ine_o;
      end
    3'd2: begin
       s_output1 <= post_norm_mul_output;
       s_ine_o <= post_norm_mul_ine;
    end
    3'd3: begin
       s_output1 <= post_norm_div_output;
       s_ine_o <= post_norm_div_ine;
    end
    //    3'd4: begin
    //          s_output1   <= post_norm_sqrt_output;
    //    s_ine_o   <= post_norm_sqrt_ine_o;
    //  end
    default: begin
       s_output1 <= 0;
       s_ine_o <= 0;
    end
  endcase // case (fpu_op_i)
     end // always @ (posedge clk)

   // Infinte exponent
   assign s_infa = &opa_r[30:23];
   assign s_infb = &opb_r[30:23];

   always @*
     begin
  if (rmode_i==2'd0 | s_div_zero_o | s_infa | s_infb | s_qnan_o |
      s_qnan_o) // Round to nearest even
    s_output_o = s_output1;
  else if (rmode_i==2'd1 & (&s_output1[30:23]))
    // In round-to-zero: the sum of two non-infinity operands is never
    // infinity,even if an overflow occures
    s_output_o = {s_output1[31], 31'b1111111_01111111_11111111_11111111};
  else if (rmode_i==2'd2 & (&s_output1[31:23]))
    // In round-up: the sum of two non-infinity operands is never
    // negative infinity,even if an overflow occures
    s_output_o = {32'b11111111_01111111_11111111_11111111};
  else if (rmode_i==2'd3) begin
     if (((fpu_op_i==3'd0) | (fpu_op_i==3'd1)) & s_zero_o &
         (opa_r[31] | (fpu_op_i[0] ^ opb_r[31])))
       // In round-down: a-a= -0
       s_output_o = {1'b1,s_output1[30:0]};
     else if (s_output1[31:23]==9'b0_11111111)
       s_output_o = 32'b01111111011111111111111111111111;
     else
       s_output_o = s_output1;
  end
  else
    s_output_o = s_output1;
     end // always @ *

   // Exception generation
   assign s_underflow_o = (s_output1[30:23]==8'h00) & s_ine_o;
   assign s_overflow_o = (s_output1[30:23]==8'hff) & s_ine_o;
   assign s_div_zero_o = serial_div_div_zero & fpu_op_i==3'd3;
   assign s_inf_o = s_output1[30:23]==8'hff & !(s_qnan_o | s_snan_o);
   assign s_zero_o = !(|s_output1[30:0]);
   assign s_qnan_o = s_output1[30:0]==QNAN;
   assign s_snan_o = s_output1[30:0]==SNAN;

endmodule // mor1kx_fpu_arith


