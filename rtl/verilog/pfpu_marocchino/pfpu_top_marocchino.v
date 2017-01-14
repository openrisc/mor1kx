/////////////////////////////////////////////////////////////////////
//                                                                 //
//    pfpu_top_marocchino                                          //
//    64-bit floating point top level for MAROCCHINO pipeline      //
//                                                                 //
//    Author: Andrey Bacherov                                      //
//            avbacherov@opencores.org                             //
//                                                                 //
/////////////////////////////////////////////////////////////////////
//                                                                 //
//   Copyright (C) 2015 Andrey Bacherov                            //
//                      avbacherov@opencores.org                   //
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

//---------------------------------------------------------------//
// Order Control Buffer for FPU64                                //
//   simplified version of mor1kx_ocb_marocchino                 //
//   it also contents only 4 order taps and only last tap's      //
//   output is required here                                     //
//---------------------------------------------------------------//

module pfpu_ocb_marocchino
(
  // clocks and resets
  input   clk,
  input   rst,
  // pipe controls
  input   pipeline_flush_i,
  input   taking_op_fpxx_arith_i,  // write: an FPU pipe is taking operands
  input   rnd_taking_op_i,       // read:  rounding engine is taking result
  // data input
  input   exec_op_fp64_arith_i,
  input   add_start_i,
  input   mul_start_i,
  input   div_start_i,
  input   i2f_start_i,
  input   f2i_start_i,
  input   res_inv_i,
  input   res_inf_i,
  input   res_snan_i,
  input   res_qnan_i,
  input   res_anan_sign_i,
  // data ouputs
  output  rnd_op_fp64_arith_o,
  output  grant_rnd_to_add_o,
  output  grant_rnd_to_mul_o,
  output  grant_rnd_to_div_o,
  output  grant_rnd_to_i2f_o,
  output  grant_rnd_to_f2i_o,
  output  ocb_inv_o,
  output  ocb_inf_o,
  output  ocb_snan_o,
  output  ocb_qnan_o,
  output  ocb_anan_sign_o,
  // "OCB is full" flag
  //   (a) external control logic must stop the "writing without reading"
  //       operation if OCB is full
  //   (b) however, the "writing + reading" is possible
  //       because it just pushes OCB and keeps it full
  output  pfpu_ocb_full_o
);

  localparam NUM_TAPS =  4;
  localparam TAP_DW   = 11;

  // "pointers"
  reg   [NUM_TAPS:0] ptr_curr; // on current active tap
  reg [NUM_TAPS-1:0] ptr_prev; // on previous active tap

  // pointers are zero: tap #0 (output) is active
  wire ptr_curr_0 = ptr_curr[0];
  wire ptr_prev_0 = ptr_prev[0];

  // "OCB is full" flag
  //  # no more availaible taps, pointer is out of range
  assign pfpu_ocb_full_o = ptr_curr[NUM_TAPS];

  // control to increment/decrement pointers
  wire rd_only = ~taking_op_fpxx_arith_i &  rnd_taking_op_i;
  wire wr_only =  taking_op_fpxx_arith_i & ~rnd_taking_op_i;
  wire wr_rd   =  taking_op_fpxx_arith_i &  rnd_taking_op_i;


  // operation algorithm:
  //-----------------------------------------------------------------------------
  // read only    | push: tap[k-1] <= tap[k], tap[num_taps-1] <= reset_value;
  //              | update pointers: if(~ptr_prev_0) ptr_prev <= (ptr_prev >> 1);
  //              |                  if(~ptr_curr_0) ptr_curr <= (ptr_curr >> 1);
  //-----------------------------------------------------------------------------
  // write only   | tap[ptr_curr] <= ocbi_i
  //              | ptr_prev <= ptr_curr;
  //              | ptr_curr <= (ptr_curr << 1);
  //-----------------------------------------------------------------------------
  // read & write | push: tap[k-1] <= tap[k]
  //              |       tap[ptr_prev] <= ocbi_i;
  //-----------------------------------------------------------------------------


  wire ptr_curr_inc = wr_only; // increment pointer on current tap
  wire ptr_curr_dec = rd_only & ~ptr_curr_0; // decrement ...
  wire ptr_prev_dec = rd_only & ~ptr_prev_0; // decrement ... previous ...

  // update pointer on current tap
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      ptr_curr <= {{NUM_TAPS{1'b0}},1'b1};
    else if(pipeline_flush_i)
      ptr_curr <= {{NUM_TAPS{1'b0}},1'b1};
    else if(ptr_curr_inc)
      ptr_curr <= (ptr_curr << 1);
    else if(ptr_curr_dec)
      ptr_curr <= (ptr_curr >> 1);
  end // @clock

  // update pointer on previous tap
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      ptr_prev <= {{(NUM_TAPS-1){1'b0}},1'b1};
    else if(pipeline_flush_i)
      ptr_prev <= {{(NUM_TAPS-1){1'b0}},1'b1};
    else if(ptr_curr_inc)
      ptr_prev <= ptr_curr[NUM_TAPS-1:0];
    else if(ptr_prev_dec)
      ptr_prev <= (ptr_prev >> 1);
  end // @clock


  // enable signals for taps
  wire [NUM_TAPS-1:0] en_curr_tap = {NUM_TAPS{wr_only}} & ptr_curr[NUM_TAPS-1:0];
  wire [NUM_TAPS-1:0] push_taps =
    en_curr_tap |                // tap[ptr_curr] <= ocbi_i (note: by wr_only)
    {NUM_TAPS{rnd_taking_op_i}}; // tap[k-1] <= tap[k]

  // control for forwarding multiplexors
  wire [NUM_TAPS-1:0] use_forwarded_value =
    en_curr_tap |                   // tap[ptr_curr] <= ocbi_i (note: by wr_only)
    ({NUM_TAPS{wr_rd}} & ptr_prev); // tap[ptr_prev] <= ocbi_i;


  // order input
  wire [(TAP_DW-1):0] ocbi = {exec_op_fp64_arith_i,
                              add_start_i, mul_start_i, div_start_i, i2f_start_i, f2i_start_i,
                              res_inv_i, res_inf_i, res_snan_i, res_qnan_i, res_anan_sign_i};

  // taps ouputs
  wire [(TAP_DW-1):0] ocbo00; // OCB output
  wire [(TAP_DW-1):0] ocbo01; // ...
  wire [(TAP_DW-1):0] ocbo02; // ...
  wire [(TAP_DW-1):0] ocbo03; // OCB entrance

  // granting flags output
  assign {rnd_op_fp64_arith_o,
          grant_rnd_to_add_o, grant_rnd_to_mul_o, grant_rnd_to_div_o, grant_rnd_to_i2f_o, grant_rnd_to_f2i_o,
          ocb_inv_o, ocb_inf_o, ocb_snan_o, ocb_qnan_o, ocb_anan_sign_o} = ocbo00;

  // taps
  //   tap #00
  ocb_tap
  #(
    .DATA_SIZE (TAP_DW)
  )
  u_tap_00
  (
    .clk                    (clk),
    .rst                    (rst),
    .flush_i                (pipeline_flush_i),
    .push_i                 (push_taps[0]),
    .prev_tap_out_i         (ocbo01),
    .forwarded_value_i      (ocbi),
    .use_forwarded_value_i  (use_forwarded_value[0]),
    .out_o                  (ocbo00)
  );

  //   tap #01
  ocb_tap
  #(
    .DATA_SIZE (TAP_DW)
  )
  u_tap_01
  (
    .clk                    (clk),
    .rst                    (rst),
    .flush_i                (pipeline_flush_i),
    .push_i                 (push_taps[1]),
    .prev_tap_out_i         (ocbo02),
    .forwarded_value_i      (ocbi),
    .use_forwarded_value_i  (use_forwarded_value[1]),
    .out_o                  (ocbo01)
  );

  //   tap #02
  ocb_tap
  #(
    .DATA_SIZE (TAP_DW)
  )
  u_tap_02
  (
    .clk                    (clk),
    .rst                    (rst),
    .flush_i                (pipeline_flush_i),
    .push_i                 (push_taps[2]),
    .prev_tap_out_i         (ocbo03),
    .forwarded_value_i      (ocbi),
    .use_forwarded_value_i  (use_forwarded_value[2]),
    .out_o                  (ocbo02)
  );

  //   tap #03 (entrance)
  ocb_tap
  #(
    .DATA_SIZE (TAP_DW)
  )
  u_tap_03
  (
    .clk                    (clk),
    .rst                    (rst),
    .flush_i                (pipeline_flush_i),
    .push_i                 (push_taps[3]),
    .prev_tap_out_i         ({TAP_DW{1'b0}}),
    .forwarded_value_i      (ocbi),
    .use_forwarded_value_i  (use_forwarded_value[3]),
    .out_o                  (ocbo03)
  );
endmodule // pfpu_ocb_marocchino


// fpu operations:
// ===================
// 0000 = add
// 0001 = substract
// 0010 = multiply
// 0011 = divide
// 0100 = i2f
// 0101 = f2i
// 0110 = unused (rem)
// 0111 = reserved
// 1xxx = comparison


module pfpu_top_marocchino
(
  // clock & reset
  input                               clk,
  input                               rst,

  // pipeline control
  input                               pipeline_flush_i,
  input                               padv_wb_i,
  input                               grant_wb_to_fpxx_arith_i,
  input                               grant_wb_to_fp64_cmp_i,

  // pipeline control outputs
  output                              fpxx_taking_op_o,
  output                              fpxx_arith_valid_o,  // WB-latching ahead arithmetic ready flag

  // Configuration
  input     [`OR1K_FPCSR_RM_SIZE-1:0] round_mode_i,
  input                               except_fpu_enable_i,
  input   [`OR1K_FPCSR_ALLF_SIZE-1:0] ctrl_fpu_mask_flags_i,

  // Commands for arithmetic part
  input                               exec_op_fp64_arith_i, // Clarification: FP64 instruction
  input                               exec_op_fpxx_add_i,
  input                               exec_op_fpxx_sub_i,
  input                               exec_op_fpxx_mul_i,
  input                               exec_op_fpxx_div_i,
  input                               exec_op_fpxx_i2f_i,
  input                               exec_op_fpxx_f2i_i,

  // Commands for comparison part
  input                         [2:0] exec_opc_fp64_cmp_i,

  // Operands from reservation station
  input                        [31:0] exec_fpxx_a1_i,
  input                        [31:0] exec_fpxx_b1_i,
  input                        [31:0] exec_fpxx_a2_i,
  input                        [31:0] exec_fpxx_b2_i,

  // FPU-64 arithmetic part
  output                       [31:0] wb_fpxx_arith_res_hi_o,   // arithmetic result
  output                       [31:0] wb_fpxx_arith_res_lo_o,   // arithmetic result 2
  output  [`OR1K_FPCSR_ALLF_SIZE-1:0] wb_fpxx_arith_fpcsr_o,    // arithmetic exceptions
  output                              wb_fpxx_arith_wb_fpcsr_o, // update FPCSR
  output                              wb_except_fpxx_arith_o,   // generate exception

  // FPU-64 comparison part
  output                              wb_fp64_flag_set_o,      // comparison result
  output                              wb_fp64_flag_clear_o,    // comparison result
  output                              wb_fp64_cmp_inv_o,       // comparison flag 'invalid'
  output                              wb_fp64_cmp_inf_o,       // comparison flag 'infinity'
  output                              wb_fp64_cmp_wb_fpcsr_o,  // update FPCSR
  output                              wb_except_fp64_cmp_o     // exception by FP64-comparison
);

// fp64 pipes controls
wire   taking_op_fpxx_arith;
wire   taking_op_fp64_cmp = padv_wb_i & grant_wb_to_fp64_cmp_i;
assign fpxx_taking_op_o   = taking_op_fpxx_arith | taking_op_fp64_cmp;

// Double precision operands A and B
wire [63:0] fp64_opa = {exec_fpxx_a1_i, ({32{exec_op_fp64_arith_i}} & exec_fpxx_a2_i)};
wire [63:0] fp64_opb = {exec_fpxx_b1_i, ({32{exec_op_fp64_arith_i}} & exec_fpxx_b2_i)};


// analysis of operand A
//   split input a
wire        signa  = fp64_opa[63];
wire [10:0] expa   = exec_op_fp64_arith_i ? fp64_opa[62:52] : ({3'd0,fp64_opa[62:55]});
wire [51:0] fracta = exec_op_fp64_arith_i ? fp64_opa[51:0]  : ({fp64_opa[54:32],29'd0});
//   detect infinity a
wire expa_ff = exec_op_fp64_arith_i ? (&fp64_opa[62:52]) : (&fp64_opa[62:55]);
wire infa    = expa_ff & (~(|fracta));
//   signaling NaN: exponent is "all ones", [51] is zero,
//                  rest of fract is non-zero
//   quiet NaN: exponent is "all ones", [51] is 1
wire snan_a = expa_ff & (~fracta[51]) & (|fracta[50:0]);
wire qnan_a = expa_ff &   fracta[51];
//   denormalized/zero of a
wire opa_0  = ~(|fp64_opa[62:0]);
wire opa_dn = (~(|expa)) & (|fracta);


// analysis of operand B
//   split input b
wire        signb  = fp64_opb[63];
wire [10:0] expb   = exec_op_fp64_arith_i ? fp64_opb[62:52] : ({3'd0,fp64_opb[62:55]});
wire [51:0] fractb = exec_op_fp64_arith_i ? fp64_opb[51:0]  : ({fp64_opb[54:32],29'd0});
//   detect infinity b
wire expb_ff = exec_op_fp64_arith_i ? (&fp64_opb[62:52]) : (&fp64_opb[62:55]);
wire infb    = expb_ff & (~(|fractb));
//   detect NaNs in b
wire snan_b = expb_ff & (~fractb[51]) & (|fractb[50:0]);
wire qnan_b = expb_ff &   fractb[51];
//   denormalized/zero of a
wire opb_0  = ~(|fp64_opb[62:0]);
wire opb_dn = (~(|expb)) & (|fractb);


// detection of some exceptions
//   a nan input -> qnan output
wire snan_x = snan_a | snan_b;
wire qnan_x = qnan_a | qnan_b;
//   sign of output nan
wire anan_sign_x = (snan_a | qnan_a) ? signa : signb;


// restored exponents
wire [12:0] exp13a = {2'd0,expa[10:1],(expa[0] | opa_dn)};
wire [12:0] exp13b = {2'd0,expb[10:1],(expb[0] | opb_dn)};
// restored fractionals
wire [52:0] fract53a = {((~opa_dn) & (~opa_0)),fracta};
wire [52:0] fract53b = {((~opb_dn) & (~opb_0)),fractb};


// Support for ADD/SUB (historically they were comparator's part)
//  # exponents
wire exp_gt = (exp13a  > exp13b);
wire exp_eq = (exp13a == exp13b);
//  # fractionals
wire fract_gt = (fract53a  > fract53b);
wire fract_eq = (fract53a == fract53b);
//  # comparisons for ADD/SUB
wire addsub_agtb = exp_gt | (exp_eq & fract_gt);
wire addsub_aeqb = exp_eq & fract_eq;


// Calculate INV,INF,SNaN,QNaN and signum(NaN)
// flags here and push them into Order Control Buffer
// till rounding engine (i.e. around computational modules).
//   ## INV:
//      ADD/SUB : (inf - inf)  -> invalid operation, snan output
//      DIV:      0/0, inf/inf -> invalid operation; snan output
//      MUL:      0 * inf      -> invalid operation; snan output
wire res_inv = ( (exec_op_fpxx_add_i | exec_op_fpxx_sub_i) &
                 infa & infb & (signa ^ (exec_op_fpxx_sub_i ^ signb)) ) |
               (  exec_op_fpxx_div_i &
                 ((opa_0 & opb_0) | (infa & infb)) )                  |
               (  exec_op_fpxx_mul_i &
                 ((opa_0 & infb) | (opb_0 & infa)) );
wire ocb_inv;
//   ## INF:
wire res_inf = ( (exec_op_fpxx_add_i | exec_op_fpxx_sub_i | exec_op_fpxx_mul_i) &
                 (infa | infb) ) |
               (  exec_op_fpxx_div_i &
                  infa );
wire ocb_inf;
//   ## SNaN:
wire res_snan = ( (exec_op_fpxx_add_i | exec_op_fpxx_sub_i |
                   exec_op_fpxx_mul_i | exec_op_fpxx_div_i |
                   exec_op_fpxx_f2i_i) ) & snan_x;
wire ocb_snan;
//   ## QNaN:
wire res_qnan = ( (exec_op_fpxx_add_i | exec_op_fpxx_sub_i |
                   exec_op_fpxx_mul_i | exec_op_fpxx_div_i |
                   exec_op_fpxx_f2i_i) ) & qnan_x;
wire ocb_qnan;
//   ## Signum (NaN):
wire res_anan_sign = ( (exec_op_fpxx_add_i | exec_op_fpxx_sub_i |
                        exec_op_fpxx_mul_i | exec_op_fpxx_div_i) ) & anan_sign_x;
wire ocb_anan_sign;


// order control buffer is full:
// we are waiting an arithmetic pipe result for rounding
wire pfpu_ocb_full;

// unit-wise control signals
//  ## ADD / SUB
wire add_start          = (exec_op_fpxx_add_i | exec_op_fpxx_sub_i) & (~pfpu_ocb_full);
wire add_taking_op;
wire add_rdy;
wire grant_rnd_to_add;
wire rnd_muxing_add     = add_rdy & grant_rnd_to_add; // to rounding input muxer
wire rnd_taking_add;

//  ## MUL
wire mul_start          = exec_op_fpxx_mul_i & (~pfpu_ocb_full);
wire mul_rdy;
wire grant_rnd_to_mul;
wire rnd_muxing_mul     = mul_rdy & grant_rnd_to_mul; // to rounding input muxer
wire rnd_taking_mul;

//  ## DIV
wire div_start          = exec_op_fpxx_div_i & (~pfpu_ocb_full);
wire div_rdy;
wire grant_rnd_to_div;
wire rnd_muxing_div     = div_rdy & grant_rnd_to_div; // to rounding input muxer
wire rnd_taking_div;

//  ## MUL/DIV
wire muldiv_taking_op;

//  ## I2F
wire i2f_start          = exec_op_fpxx_i2f_i & (~pfpu_ocb_full);
wire i2f_taking_op;
wire i2f_rdy;
wire grant_rnd_to_i2f;
wire rnd_muxing_i2f     = i2f_rdy & grant_rnd_to_i2f; // to rounding input muxer
wire rnd_taking_i2f;

//  ## F2I
wire f2i_start          = exec_op_fpxx_f2i_i & (~pfpu_ocb_full);
wire f2i_taking_op;
wire f2i_rdy;
wire grant_rnd_to_f2i;
wire rnd_muxing_f2i     = f2i_rdy & grant_rnd_to_f2i; // to rounding input muxer
wire rnd_taking_f2i;

// feedback to drop FP32 arithmetic related command
assign taking_op_fpxx_arith = add_taking_op | muldiv_taking_op | i2f_taking_op | f2i_taking_op;

// rounding engine takes an OP
wire rnd_taking_op = rnd_taking_add | rnd_taking_mul | rnd_taking_div |
                     rnd_taking_i2f | rnd_taking_f2i;

// FP32/FP64 clarification for rounding
wire rnd_op_fp64_arith;


// PFPU [O]rder [C]ontrol [B]uffer instance
pfpu_ocb_marocchino  u_pfpu_ocb
(
  // clocks and resets
  .clk                    (clk), // PFPU_OCB
  .rst                    (rst), // PFPU_OCB
  // pipe controls
  .pipeline_flush_i       (pipeline_flush_i), // PFPU_OCB
  .taking_op_fpxx_arith_i (taking_op_fpxx_arith), // PFPU_OCB
  .rnd_taking_op_i        (rnd_taking_op), // PFPU_OCB
  // data input
  .exec_op_fp64_arith_i   (exec_op_fp64_arith_i), // PFPU_OCB
  .add_start_i            (add_start), // PFPU_OCB
  .mul_start_i            (mul_start), // PFPU_OCB
  .div_start_i            (div_start), // PFPU_OCB
  .i2f_start_i            (i2f_start), // PFPU_OCB
  .f2i_start_i            (f2i_start), // PFPU_OCB
  .res_inv_i              (res_inv), // PFPU_OCB
  .res_inf_i              (res_inf), // PFPU_OCB
  .res_snan_i             (res_snan), // PFPU_OCB
  .res_qnan_i             (res_qnan), // PFPU_OCB
  .res_anan_sign_i        (res_anan_sign), // PFPU_OCB
  // data ouputs
  .rnd_op_fp64_arith_o    (rnd_op_fp64_arith), // PFPU_OCB
  .grant_rnd_to_add_o     (grant_rnd_to_add), // PFPU_OCB
  .grant_rnd_to_mul_o     (grant_rnd_to_mul), // PFPU_OCB
  .grant_rnd_to_div_o     (grant_rnd_to_div), // PFPU_OCB
  .grant_rnd_to_i2f_o     (grant_rnd_to_i2f), // PFPU_OCB
  .grant_rnd_to_f2i_o     (grant_rnd_to_f2i), // PFPU_OCB
  .ocb_inv_o              (ocb_inv), // PFPU_OCB
  .ocb_inf_o              (ocb_inf), // PFPU_OCB
  .ocb_snan_o             (ocb_snan), // PFPU_OCB
  .ocb_qnan_o             (ocb_qnan), // PFPU_OCB
  .ocb_anan_sign_o        (ocb_anan_sign), // PFPU_OCB
  // "OCB is full" flag
  .pfpu_ocb_full_o        (pfpu_ocb_full) // PFPU_OCB
);


// Addition / Substruction
//   connection wires
wire        add_sign;      // add/sub signum
wire        add_sub_0;     // flag that actual substruction is performed and result is zero
wire  [5:0] add_shl;       // do left shift in align stage
wire [12:0] add_exp13shl;  // exponent for left shift align
wire [12:0] add_exp13sh0;  // exponent for no shift in align
wire [56:0] add_fract57;   // fractional with appended {r,s} bits
//   module istance
pfpu_addsub_marocchino u_pfpu_addsub
(
  // clocks and resets
  .clk                    (clk), // PFPU_ADDSUB
  .rst                    (rst), // PFPU_ADDSUB
  // ADD/SUB pipe controls
  .pipeline_flush_i       (pipeline_flush_i), // PFPU_ADDSUB
  .add_start_i            (add_start), // PFPU_ADDSUB
  .exec_op_fpxx_sub_i     (exec_op_fpxx_sub_i), // PFPU_ADDSUB
  .add_taking_op_o        (add_taking_op), // PFPU_ADDSUB
  .add_rdy_o              (add_rdy), // PFPU_ADDSUB
  .rnd_taking_add_i       (rnd_taking_add), // PFPU_ADDSUB
  // input 'a' related values
  .signa_i                (signa), // PFPU_ADDSUB
  .exp13a_i               (exp13a), // PFPU_ADDSUB
  .fract53a_i             (fract53a), // PFPU_ADDSUB
  // input 'b' related values
  .signb_i                (signb), // PFPU_ADDSUB
  .exp13b_i               (exp13b), // PFPU_ADDSUB
  .fract53b_i             (fract53b), // PFPU_ADDSUB
  // 'a'/'b' related
  .exec_op_fp64_arith_i   (exec_op_fp64_arith_i), // PFPU_ADDSUB
  .opc_0_i                (infa | infb), // PFPU_ADDSUB
  .addsub_agtb_i          (addsub_agtb), // PFPU_ADDSUB
  .addsub_aeqb_i          (addsub_aeqb), // PFPU_ADDSUB
  // outputs
  .add_sign_o             (add_sign), // PFPU_ADDSUB
  .add_sub_0_o            (add_sub_0), // PFPU_ADDSUB
  .add_shl_o              (add_shl), // PFPU_ADDSUB
  .add_exp13shl_o         (add_exp13shl), // PFPU_ADDSUB
  .add_exp13sh0_o         (add_exp13sh0), // PFPU_ADDSUB
  .add_fract57_o          (add_fract57) // PFPU_ADDSUB
);


// MUL/DIV pipeline
//   MUL outputs
wire        mul_sign;      // mul signum
wire  [5:0] mul_shr;       // do right shift in align stage
wire [12:0] mul_exp13shr;  // exponent for right shift align
wire [12:0] mul_exp13sh0;  // exponent for no shift in align
wire [56:0] mul_fract57;   // fractional with appended {r,s} bits
// DIV outputs
wire        div_sign;      // signum
wire  [5:0] div_shr;       // do right shift in align stage
wire [12:0] div_exp13shr;  // exponent for right shift align
wire        div_shl;       // do left shift in align stage
wire [12:0] div_exp13shl;  // exponent for left shift align
wire [12:0] div_exp13sh0;  // exponent for no shift in align
wire [56:0] div_fract57;   // fractional with appended {r,s} bits
wire        div_dbz;        // div division by zero flag
//   module istance
pfpu_muldiv_marocchino u_pfpu_muldiv
(
  // clocks and resets
  .clk                    (clk), // PFPU_MULDIV
  .rst                    (rst), // PFPU_MULDIV
  // pipe controls
  .pipeline_flush_i       (pipeline_flush_i), // PFPU_MULDIV
  .mul_start_i            (mul_start), // PFPU_MULDIV
  .div_start_i            (div_start), // PFPU_MULDIV
  .muldiv_taking_op_o     (muldiv_taking_op), // PFPU_MULDIV
  .mul_rdy_o              (mul_rdy), // PFPU_MULDIV
  .rnd_taking_mul_i       (rnd_taking_mul), // PFPU_MULDIV
  .div_rdy_o              (div_rdy), // PFPU_MULDIV
  .rnd_taking_div_i       (rnd_taking_div), // PFPU_MULDIV
  // input 'a' related values
  .signa_i                (signa), // PFPU_MULDIV
  .exp13a_i               (exp13a), // PFPU_MULDIV
  .fract53a_i             (fract53a), // PFPU_MULDIV
  // input 'b' related values
  .signb_i                (signb), // PFPU_MULDIV
  .exp13b_i               (exp13b), // PFPU_MULDIV
  .fract53b_i             (fract53b), // PFPU_MULDIV
  // 'a'/'b' related
  .exec_op_fp64_arith_i   (exec_op_fp64_arith_i), // PFPU_MULDIV
  .dbz_i                  (exec_op_fpxx_div_i & (~opa_0) & (~infa) & opb_0), // PFPU_MULDIV
  .opc_0_i                (opa_0 | opb_0 | (exec_op_fpxx_div_i & (infa | infb))), // PFPU_MULDIV
  // MUL outputs
  .mul_sign_o             (mul_sign), // PFPU_MULDIV
  .mul_shr_o              (mul_shr), // PFPU_MULDIV
  .mul_exp13shr_o         (mul_exp13shr), // PFPU_MULDIV
  .mul_exp13sh0_o         (mul_exp13sh0), // PFPU_MULDIV
  .mul_fract57_o          (mul_fract57), // PFPU_MULDIV
  // DIV outputs
  .div_sign_o             (div_sign), // PFPU_MULDIV
  .div_shr_o              (div_shr), // PFPU_MULDIV
  .div_exp13shr_o         (div_exp13shr), // PFPU_MULDIV
  .div_shl_o              (div_shl), // PFPU_MULDIV
  .div_exp13shl_o         (div_exp13shl), // PFPU_MULDIV
  .div_exp13sh0_o         (div_exp13sh0), // PFPU_MULDIV
  .div_fract57_o          (div_fract57), // PFPU_MULDIV
  .div_dbz_o              (div_dbz) // PFPU_MULDIV
);


// convertors
//   i2f connection wires
wire        i2f_sign;
wire  [3:0] i2f_shr;
wire [10:0] i2f_exp11shr;
wire  [5:0] i2f_shl;
wire [10:0] i2f_exp11shl;
wire [10:0] i2f_exp11sh0;
wire [63:0] i2f_fract64;
//   i2f module instance
pfpu_i2f_marocchino u_pfpu_i2f
(
  // clocks and resets
  .clk                    (clk), // PFPU_I2F
  .rst                    (rst), // PFPU_I2F
  // I2F pipe controls
  .pipeline_flush_i       (pipeline_flush_i), // PFPU_I2F
  .start_i                (i2f_start), // PFPU_I2F
  .i2f_taking_op_o        (i2f_taking_op), // PFPU_I2F
  .i2f_rdy_o              (i2f_rdy), // PFPU_I2F
  .rnd_taking_i2f_i       (rnd_taking_i2f), // PFPU_I2F
  // operand for conversion
  .opa_i                  (fp64_opa), // PFPU_I2F
  .exec_op_fp64_arith_i   (exec_op_fp64_arith_i), // PFPU_I2F
  // ouputs for rounding
  .i2f_sign_o             (i2f_sign), // PFPU_I2F
  .i2f_shr_o              (i2f_shr), // PFPU_I2F
  .i2f_exp11shr_o         (i2f_exp11shr), // PFPU_I2F
  .i2f_shl_o              (i2f_shl), // PFPU_I2F
  .i2f_exp11shl_o         (i2f_exp11shl), // PFPU_I2F
  .i2f_exp11sh0_o         (i2f_exp11sh0), // PFPU_I2F
  .i2f_fract64_o          (i2f_fract64) // PFPU_I2F
);


//   f2i connection wires
wire        f2i_sign;      // f2i signum
wire [52:0] f2i_int53;     // f2i fractional
wire  [5:0] f2i_shr;       // f2i required shift right value
wire  [3:0] f2i_shl;       // f2i required shift left value
wire        f2i_ovf;       // f2i overflow flag
//    f2i module instance
pfpu_f2i_marocchino u_pfpu_f2i
(
  // clocks and resets
  .clk                  (clk), // PFPU_F2I
  .rst                  (rst), // PFPU_F2I
  // pipe controls
  .pipeline_flush_i     (pipeline_flush_i), // PFPU_F2I
  .start_i              (f2i_start), // PFPU_F2I
  .f2i_taking_op_o      (f2i_taking_op), // PFPU_F2I
  .f2i_rdy_o            (f2i_rdy), // PFPU_F2I
  .rnd_taking_f2i_i     (rnd_taking_f2i), // PFPU_F2I
  // input data
  .signa_i              (signa), // PFPU_F2I
  .exp13a_i             (exp13a), // PFPU_F2I
  .fract53a_i           (fract53a), // PFPU_F2I
  .exec_op_fp64_arith_i (exec_op_fp64_arith_i), // PFPU_F2I
  .snan_i               (snan_x), // PFPU_F2I
  .qnan_i               (qnan_x), // PFPU_F2I
  // output data for rounding
  .f2i_sign_o           (f2i_sign), // PFPU_F2I
  .f2i_int53_o          (f2i_int53), // PFPU_F2I
  .f2i_shr_o            (f2i_shr), // PFPU_F2I
  .f2i_shl_o            (f2i_shl), // PFPU_F2I
  .f2i_ovf_o            (f2i_ovf) // PFPU_F2I
);


// multiplexing and rounding
pfpu_rnd_marocchino u_pfpu_rnd
(
  // clocks, resets
  .clk                      (clk), // PFPU_RND
  .rst                      (rst), // PFPU_RND
  // pipe controls
  .pipeline_flush_i         (pipeline_flush_i), // PFPU_RND
  .rnd_taking_add_o         (rnd_taking_add), // PFPU_RND
  .rnd_taking_mul_o         (rnd_taking_mul), // PFPU_RND
  .rnd_taking_div_o         (rnd_taking_div), // PFPU_RND
  .rnd_taking_i2f_o         (rnd_taking_i2f), // PFPU_RND
  .rnd_taking_f2i_o         (rnd_taking_f2i), // PFPU_RND
  .fpxx_arith_valid_o       (fpxx_arith_valid_o), // PFPU_RND
  .padv_wb_i                (padv_wb_i), // PFPU_RND
  .grant_wb_to_fpxx_arith_i (grant_wb_to_fpxx_arith_i), // PFPU_RND
  // configuration
  .rmode_i                  (round_mode_i), // PFPU_RND
  .except_fpu_enable_i      (except_fpu_enable_i), // PFPU_RND
  .ctrl_fpu_mask_flags_i    (ctrl_fpu_mask_flags_i), // PFPU_RND
  // from add/sub
  .add_rdy_i                (rnd_muxing_add), // PFPU_RND
  .add_sign_i               (add_sign), // PFPU_RND
  .add_sub_0_i              (add_sub_0), // PFPU_RND
  .add_shl_i                (add_shl), // PFPU_RND
  .add_exp13shl_i           (add_exp13shl), // PFPU_RND
  .add_exp13sh0_i           (add_exp13sh0), // PFPU_RND
  .add_fract57_i            (add_fract57), // PFPU_RND
  // from mul
  .mul_rdy_i                (rnd_muxing_mul), // PFPU_RND
  .mul_sign_i               (mul_sign), // PFPU_RND
  .mul_shr_i                (mul_shr), // PFPU_RND
  .mul_exp13shr_i           (mul_exp13shr), // PFPU_RND
  .mul_exp13sh0_i           (mul_exp13sh0), // PFPU_RND
  .mul_fract57_i            (mul_fract57), // PFPU_RND
  // from div
  .div_rdy_i                (rnd_muxing_div), // PFPU_RND
  .div_sign_i               (div_sign), // PFPU_RND
  .div_shr_i                (div_shr), // PFPU_RND
  .div_exp13shr_i           (div_exp13shr), // PFPU_RND
  .div_shl_i                (div_shl), // PFPU_RND
  .div_exp13shl_i           (div_exp13shl), // PFPU_RND
  .div_exp13sh0_i           (div_exp13sh0), // PFPU_RND
  .div_fract57_i            (div_fract57), // PFPU_RND
  .div_dbz_i                (div_dbz), // PFPU_RND
  // from i2f
  .i2f_rdy_i                (rnd_muxing_i2f), // PFPU_RND
  .i2f_sign_i               (i2f_sign), // PFPU_RND
  .i2f_shr_i                (i2f_shr), // PFPU_RND
  .i2f_exp11shr_i           (i2f_exp11shr), // PFPU_RND
  .i2f_shl_i                (i2f_shl), // PFPU_RND
  .i2f_exp11shl_i           (i2f_exp11shl), // PFPU_RND
  .i2f_exp11sh0_i           (i2f_exp11sh0), // PFPU_RND
  .i2f_fract64_i            (i2f_fract64), // PFPU_RND
  // from f2i
  .f2i_rdy_i                (rnd_muxing_f2i), // PFPU_RND
  .f2i_sign_i               (f2i_sign), // PFPU_RND
  .f2i_int53_i              (f2i_int53), // PFPU_RND
  .f2i_shr_i                (f2i_shr), // PFPU_RND
  .f2i_shl_i                (f2i_shl), // PFPU_RND
  .f2i_ovf_i                (f2i_ovf), // PFPU_RND
  // from order control buffer
  .rnd_op_fp64_arith_i      (rnd_op_fp64_arith), // PFPU_RND
  .ocb_inv_i                (ocb_inv), // PFPU_RND
  .ocb_inf_i                (ocb_inf), // PFPU_RND
  .ocb_snan_i               (ocb_snan), // PFPU_RND
  .ocb_qnan_i               (ocb_qnan), // PFPU_RND
  .ocb_anan_sign_i          (ocb_anan_sign), // PFPU_RND
  // output WB latches
  .wb_fpxx_arith_res_hi_o   (wb_fpxx_arith_res_hi_o), // PFPU_RND
  .wb_fpxx_arith_res_lo_o   (wb_fpxx_arith_res_lo_o), // PFPU_RND
  .wb_fpxx_arith_fpcsr_o    (wb_fpxx_arith_fpcsr_o), // PFPU_RND
  .wb_fpxx_arith_wb_fpcsr_o (wb_fpxx_arith_wb_fpcsr_o), // PFPU_RND
  .wb_except_fpxx_arith_o   (wb_except_fpxx_arith_o) // PFPU_RND
);


// FP64 Comparison
pfpu64_fcmp_marocchino u_fp64_cmp
(
  // clock and reset
  .clk                        (clk), // FP64_CMP
  .rst                        (rst), // FP64_CMP
  // pipeline controls
  .pipeline_flush_i           (pipeline_flush_i), // FP64_CMP
  .padv_wb_i                  (padv_wb_i), // FP64_CMP
  .grant_wb_to_fp64_cmp_i     (grant_wb_to_fp64_cmp_i), // FP64_CMP
  // command
  .opc_fp64_cmp_i             (exec_opc_fp64_cmp_i), // FP64_CMP
  // data related to operand A
  .signa_i                    (signa), // FP64_CMP
  .opa_0_i                    (opa_0), // FP64_CMP
  .infa_i                     (infa), // FP64_CMP
  // data related to operand B
  .signb_i                    (signb), // FP64_CMP
  .opb_0_i                    (opb_0), // FP64_CMP
  .infb_i                     (infb), // FP64_CMP
  // data related to operand A|B
  .snan_i                     (snan_x), // FP64_CMP
  .qnan_i                     (qnan_x), // FP64_CMP
  .exp_gt_i                   (exp_gt), // FP64_CMP
  .exp_eq_i                   (exp_eq), // FP64_CMP
  .fract_gt_i                 (fract_gt), // FP64_CMP
  .fract_eq_i                 (fract_eq), // FP64_CMP
  // Modes
  .except_fpu_enable_i        (except_fpu_enable_i), // FP64_CMP
  .ctrl_fpu_mask_flags_inv_i  (ctrl_fpu_mask_flags_i[`OR1K_FPCSR_IVF - `OR1K_FPCSR_OVF]), // FP64_CMP
  .ctrl_fpu_mask_flags_inf_i  (ctrl_fpu_mask_flags_i[`OR1K_FPCSR_INF - `OR1K_FPCSR_OVF]), // FP64_CMP
  // Outputs
  //  # WB-latched
  .wb_fp64_flag_set_o         (wb_fp64_flag_set_o), // FP64_CMP
  .wb_fp64_flag_clear_o       (wb_fp64_flag_clear_o), // FP64_CMP
  .wb_fp64_cmp_inv_o          (wb_fp64_cmp_inv_o), // FP64_CMP
  .wb_fp64_cmp_inf_o          (wb_fp64_cmp_inf_o), // FP64_CMP
  .wb_fp64_cmp_wb_fpcsr_o     (wb_fp64_cmp_wb_fpcsr_o), // FP64_CMP
  .wb_except_fp64_cmp_o       (wb_except_fp64_cmp_o) // FP64_CMP
);

endmodule // pfpu_top_marocchino
