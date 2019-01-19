/////////////////////////////////////////////////////////////////////
//                                                                 //
//    pfpu_cmp_marocchino                                          //
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
//    Modified by Andrey Bacherov, 2014-2018                       //
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

module pfpu_cmp_marocchino
(
  // clock and reset
  input              cpu_clk,
  // pipeline controls
  input              pipeline_flush_i,     // flush pipe
  output             taking_op_fpxx_cmp_o,
  input              padv_wrbk_i,            // advance output latches
  input              grant_wrbk_to_fpxx_cmp_i,
  // command
  input              op_fpxx_cmp_i,
  input        [2:0] opc_fpxx_cmp_i,
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
  input              fpu_mask_flags_inv_i,
  input              fpu_mask_flags_inf_i,
  // Outputs
  //  # pre Write-Back
  output reg         fpxx_cmp_valid_o,
  output             exec_except_fpxx_cmp_o, // exception by FP32-comparison
  //  # Write-Back-latched
  output reg         wrbk_fpxx_flag_set_o,      // comparison result
  output reg         wrbk_fpxx_flag_clear_o,    // comparison result
  output reg         wrbk_fpxx_cmp_inv_o,       // comparison flag 'invalid'
  output reg         wrbk_fpxx_cmp_inf_o,       // comparison flag 'infinity'
  output reg         wrbk_fpxx_cmp_fpcsr_we_o,  // update FPCSR
  output reg         wrbk_except_fpxx_cmp_o     // exception by FP32-comparison
);

  /*
     Any stage's output is registered.
     Definitions:
       s??o_name - "S"tage number "??", "O"utput
       s??t_name - "S"tage number "??", "T"emporary (internally)
  */

  localparam FP_OPC_SFEQ = 3'b000;
  localparam FP_OPC_SFNE = 3'b001;
  localparam FP_OPC_SFGT = 3'b010;
  localparam FP_OPC_SFGE = 3'b011;
  localparam FP_OPC_SFLT = 3'b100;
  localparam FP_OPC_SFLE = 3'b101;


  // Comparison pipe controls
  //  ## Write-Back tacking comparison result
  reg  wrbk_fpxx_cmp_miss_r;
  //  ## ready flags of stages
  reg  s1o_ready;
  //  ## per stage busy flags
  wire s1_busy = s1o_ready & wrbk_fpxx_cmp_miss_r;
  //  ## per stage advance
  wire s1_adv  = op_fpxx_cmp_i & (~s1_busy);

  // ADD/SUB pipe takes operands for computation
  assign taking_op_fpxx_cmp_o = s1_adv;


  /**** Stage #1: just output latches ****/

  reg  [2:0] s1o_opc_fpxx_cmp;
  // data related to operand A
  reg        s1o_signa;
  reg        s1o_opa_0;
  reg        s1o_infa;
  // data related to operand B
  reg        s1o_signb;
  reg        s1o_opb_0;
  reg        s1o_infb;
  // data related to operand A|B
  reg        s1o_snan;
  reg        s1o_qnan;
  reg        s1o_exp_gt;
  reg        s1o_exp_eq;
  reg        s1o_fract_gt;
  reg        s1o_fract_eq;

  // ---
  always @(posedge cpu_clk) begin
    if (s1_adv) begin
      s1o_opc_fpxx_cmp <= opc_fpxx_cmp_i;
      // data related to operand A
      s1o_signa <= signa_i;
      s1o_opa_0 <= opa_0_i;
      s1o_infa  <= infa_i;
      // data related to operand B
      s1o_signb <= signb_i;
      s1o_opb_0 <= opb_0_i;
      s1o_infb  <= infb_i;
      // data related to operand A|B
      s1o_snan     <= snan_i;
      s1o_qnan     <= qnan_i;
      s1o_exp_gt   <= exp_gt_i;
      s1o_exp_eq   <= exp_eq_i;
      s1o_fract_gt <= fract_gt_i;
      s1o_fract_eq <= fract_eq_i;
    end
  end // @clock

  // ready is special case
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      s1o_ready <= 1'b0;
    else if (s1_adv)
      s1o_ready <= 1'b1;
    else if (~wrbk_fpxx_cmp_miss_r)
      s1o_ready <= 1'b0;
  end // @clock

  //  valid flag
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      fpxx_cmp_valid_o <= 1'b0;
    else if (s1_adv)
      fpxx_cmp_valid_o <= 1'b1;
    else if (padv_wrbk_i & grant_wrbk_to_fpxx_cmp_i)
      fpxx_cmp_valid_o <= wrbk_fpxx_cmp_miss_r ? s1o_ready : 1'b0;
  end // @clock


  ////////////////////////////////////////////////////////////////////////
  // Exception Logic
  wire anan = s1o_qnan | s1o_snan;
  // Comparison invalid when sNaN in on an equal comparison,
  // or any NaN for any other comparison.
  wire inv_cmp = (s1o_snan & (s1o_opc_fpxx_cmp == FP_OPC_SFEQ)) |
                 (anan     & (s1o_opc_fpxx_cmp != FP_OPC_SFEQ));


  ////////////////////////////////////////////////////////////////////////
  // Comparison Logic
  wire exp_lt   = (~s1o_exp_gt) & (~s1o_exp_eq); // in_exp11a  < in_exp11b;
  wire fract_lt = (~s1o_fract_gt) & (~s1o_fract_eq); // in_fract53a  < in_fract53b;

  wire all_zero = s1o_opa_0 & s1o_opb_0;

  reg altb, blta, aeqb;

  always @(    s1o_qnan or      s1o_snan or  s1o_infa or s1o_infb or
              s1o_signa or     s1o_signb or
             s1o_exp_eq or    s1o_exp_gt or    exp_lt or
           s1o_fract_eq or  s1o_fract_gt or  fract_lt or  all_zero) begin
    casez( {(s1o_qnan | s1o_snan),
                         s1o_infa,      s1o_infb,
                        s1o_signa,     s1o_signb,
                       s1o_exp_eq,    s1o_exp_gt,    exp_lt,
                     s1o_fract_eq,  s1o_fract_gt,  fract_lt,
                                                   all_zero})
      12'b0_11_00_???_???_?: {blta, altb, aeqb} = 3'b001; // both op INF comparisson
      12'b0_11_01_???_???_?: {blta, altb, aeqb} = 3'b100;
      12'b0_11_10_???_???_?: {blta, altb, aeqb} = 3'b010;
      12'b0_11_11_???_???_?: {blta, altb, aeqb} = 3'b001;

      12'b0_10_00_???_???_?: {blta, altb, aeqb} = 3'b100; // opa_i INF comparisson
      12'b0_10_01_???_???_?: {blta, altb, aeqb} = 3'b100;
      12'b0_10_10_???_???_?: {blta, altb, aeqb} = 3'b010;
      12'b0_10_11_???_???_?: {blta, altb, aeqb} = 3'b010;

      12'b0_01_00_???_???_?: {blta, altb, aeqb} = 3'b010; // opb_i INF comparisson
      12'b0_01_01_???_???_?: {blta, altb, aeqb} = 3'b100;
      12'b0_01_10_???_???_?: {blta, altb, aeqb} = 3'b010;
      12'b0_01_11_???_???_?: {blta, altb, aeqb} = 3'b100;

      12'b0_00_10_???_???_0: {blta, altb, aeqb} = 3'b010; //compare base on sign
      12'b0_00_01_???_???_0: {blta, altb, aeqb} = 3'b100; //compare base on sign

      12'b0_00_??_???_???_1: {blta, altb, aeqb} = 3'b001; //compare base on sign both are zero

      12'b0_00_00_010_???_?: {blta, altb, aeqb} = 3'b100; // cmp exp, equal sign
      12'b0_00_00_001_???_?: {blta, altb, aeqb} = 3'b010;
      12'b0_00_11_010_???_?: {blta, altb, aeqb} = 3'b010;
      12'b0_00_11_001_???_?: {blta, altb, aeqb} = 3'b100;

      12'b0_00_00_100_010_?: {blta, altb, aeqb} = 3'b100; // compare fractions, equal sign, equal exp
      12'b0_00_00_100_001_?: {blta, altb, aeqb} = 3'b010;
      12'b0_00_11_100_010_?: {blta, altb, aeqb} = 3'b010;
      12'b0_00_11_100_001_?: {blta, altb, aeqb} = 3'b100;

      12'b0_00_00_100_100_?: {blta, altb, aeqb} = 3'b001;
      12'b0_00_11_100_100_?: {blta, altb, aeqb} = 3'b001;

      default: {blta, altb, aeqb} = 3'b000; // including NaNs
    endcase
  end // @ clock


  ////////////////////////////////////////////////////////////////////////
  // Comparison cmp_flag generation
  reg cmp_flag;
  always @(altb or blta or aeqb or s1o_opc_fpxx_cmp) begin
    // synthesis parallel_case
    case(s1o_opc_fpxx_cmp)
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
  // Write-Back-miss flag
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i)
      wrbk_fpxx_cmp_miss_r <= 1'b0;
    else if (padv_wrbk_i & grant_wrbk_to_fpxx_cmp_i)
      wrbk_fpxx_cmp_miss_r <= 1'b0;
    else if (~wrbk_fpxx_cmp_miss_r)
      wrbk_fpxx_cmp_miss_r <= s1o_ready;
  end // @clock

  ////////////////////////////////////////////////////////////////////////
  // Just before latching

  //  # set/slear commands
  wire s2t_fpxx_flag_set   =  cmp_flag;
  wire s2t_fpxx_flag_clear = ~cmp_flag;
  //  # FP32 comparison flags
  wire s2t_fpxx_cmp_inv    = fpu_mask_flags_inv_i & inv_cmp;
  wire s2t_fpxx_cmp_inf    = fpu_mask_flags_inf_i & (s1o_infa | s1o_infb);

  reg fpxx_flag_set_p;
  reg fpxx_flag_clear_p;
  reg fpxx_cmp_inv_p;
  reg fpxx_cmp_inf_p;

  always @(posedge cpu_clk) begin
    if (~wrbk_fpxx_cmp_miss_r) begin
      fpxx_flag_set_p   <= s2t_fpxx_flag_set;
      fpxx_flag_clear_p <= s2t_fpxx_flag_clear;
      fpxx_cmp_inv_p    <= s2t_fpxx_cmp_inv;
      fpxx_cmp_inf_p    <= s2t_fpxx_cmp_inf;
    end
  end

  //  # FP32 comparison exception
  wire   mux_except_fpxx_cmp    = (wrbk_fpxx_cmp_miss_r ? (fpxx_cmp_inv_p | fpxx_cmp_inf_p) : (s2t_fpxx_cmp_inv | s2t_fpxx_cmp_inf)) &
                                  except_fpu_enable_i;
  // ---
  assign exec_except_fpxx_cmp_o = grant_wrbk_to_fpxx_cmp_i & mux_except_fpxx_cmp;

  ////////////////////////////////////////////////////////////////////////
  // Write-Back latches: 
  always @(posedge cpu_clk) begin
    if (padv_wrbk_i & grant_wrbk_to_fpxx_cmp_i) begin
      // flag set/clear
      wrbk_fpxx_flag_set_o     <= wrbk_fpxx_cmp_miss_r ? fpxx_flag_set_p : s2t_fpxx_flag_set;
      wrbk_fpxx_flag_clear_o   <= wrbk_fpxx_cmp_miss_r ? fpxx_flag_clear_p : s2t_fpxx_flag_clear;
      // comparison exception flags
      wrbk_fpxx_cmp_inv_o      <= wrbk_fpxx_cmp_miss_r ? fpxx_cmp_inv_p : s2t_fpxx_cmp_inv;
      wrbk_fpxx_cmp_inf_o      <= wrbk_fpxx_cmp_miss_r ? fpxx_cmp_inf_p : s2t_fpxx_cmp_inf;
      wrbk_except_fpxx_cmp_o   <= mux_except_fpxx_cmp;
      // update FPCSR
      wrbk_fpxx_cmp_fpcsr_we_o <= 1'b1;
    end
    else begin
      // flag set/clear
      wrbk_fpxx_flag_set_o     <= 1'b0; // 1-clk-length
      wrbk_fpxx_flag_clear_o   <= 1'b0; // 1-clk-length
      // comparison exception flags
      wrbk_fpxx_cmp_inv_o      <= 1'b0; // 1-clk-length
      wrbk_fpxx_cmp_inf_o      <= 1'b0; // 1-clk-length
      wrbk_except_fpxx_cmp_o   <= 1'b0; // 1-clk-length
      // update FPCSR
      wrbk_fpxx_cmp_fpcsr_we_o <= 1'b0; // 1-clk-length
    end // advance Write-Back latches
  end // @clock

endmodule // pfpu_cmp_marocchino
