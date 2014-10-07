/////////////////////////////////////////////////////////////////////
////                                                             ////
////  mor1kx_fpu_intfloat_conv_except                            ////
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

module mor1kx_fpu_intfloat_conv_except
(
   input    clk,
   input    rst,
   input    [31:0] opa, opb,
   output reg inf, ind, qnan, snan, opa_nan, opb_nan,
   output reg opa_00, opb_00,
   output reg opa_inf, opb_inf
);

   ////////////////////////////////////////////////////////////////////////
   //
   // Local Wires and registers
   //

   wire [7:0]     expa, expb;   // alias to opX exponent
   wire [22:0]    fracta, fractb;   // alias to opX fraction
   reg      expa_ff, infa_f_r, qnan_r_a, snan_r_a;
   reg      expb_ff, infb_f_r, qnan_r_b, snan_r_b;
   reg      expa_00, expb_00;
   reg      fracta_00, fractb_00;

   ////////////////////////////////////////////////////////////////////////
   //
   // Aliases
   //

   assign   expa = opa[30:23];
   assign   expb = opb[30:23];
   assign fracta = opa[22:0];
   assign fractb = opb[22:0];

   ////////////////////////////////////////////////////////////////////////
   //
   // Determine if any of the input operators is a INF or NAN or any other
   // special number
   //
   always @(posedge clk `OR_ASYNC_RST)
   if (rst) begin
     expa_ff <=  0;
     expb_ff <=  0;
     infa_f_r <= 0;
     infb_f_r <= 0;
     qnan_r_a <= 0;
     snan_r_a <= 0;
     qnan_r_b <= 0;
     snan_r_b <= 0;
     ind  <= 0;
     inf  <= 0;
     qnan <= 0;
     snan <= 0;
     opa_nan <= 0;
     opb_nan <= 0;
     opa_inf <= 0;
     opb_inf <= 0;
     expa_00 <= 0;
     expb_00 <= 0;
     fracta_00 <= 0;
     fractb_00 <= 0;
     opa_00 <= 0;
     opb_00 <= 0;
   end
   else begin
     expa_ff <=  &expa;
     expb_ff <=  &expb;
     infa_f_r <=  !(|fracta);
     infb_f_r <=  !(|fractb);
     qnan_r_a <=   fracta[22];
     snan_r_a <=  !fracta[22] & |fracta[21:0];
     qnan_r_b <=   fractb[22];
     snan_r_b <=  !fractb[22]; // & |fractb[21:0];
     ind  <=  (expa_ff & infa_f_r); // & (expb_ff & infb_f_r);
     inf  <=  (expa_ff & infa_f_r); // | (expb_ff & infb_f_r);
     qnan <=  (expa_ff & qnan_r_a); // | (expb_ff & qnan_r_b);
     snan <=  (expa_ff & snan_r_a); // | (expb_ff & snan_r_b);
     opa_nan <=  &expa & (|fracta[22:0]);
     opb_nan <=  &expb & (|fractb[22:0]);
     opa_inf <=  (expa_ff & infa_f_r);
     opb_inf <=  (expb_ff & infb_f_r);
     expa_00 <=  !(|expa);
     expb_00 <=  !(|expb);
     fracta_00 <=  !(|fracta);
     fractb_00 <=  !(|fractb);
     opa_00 <=  expa_00 & fracta_00;
     opb_00 <=  expb_00 & fractb_00;
   end

endmodule // mor1kx_fpu_intfloat_conv_except
