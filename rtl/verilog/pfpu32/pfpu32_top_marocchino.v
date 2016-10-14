/////////////////////////////////////////////////////////////////////
////                                                             ////
////  pfpu32_top_marocchino                                      ////
////  32-bit floating point top level for MAROCCHINO pipeline    ////
////                                                             ////
////  Author: Andrey Bacherov                                    ////
////          avbacherov@opencores.org                           ////
////                                                             ////
/////////////////////////////////////////////////////////////////////
////                                                             ////
//// Copyright (C) 2015 Andrey Bacherov                          ////
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

`include "mor1kx-defines.v"

//---------------------------------------------------------------//
// Order Control Buffer for FPU32                                //
//   simplified version of mor1kx_ocb_marocchino                 //
//   it also contents only 4 order taps and only last tap's      //
//   output is required here                                     //
//---------------------------------------------------------------//

module pfpu32_ocb_marocchino
(
  // clocks and resets
  input   clk,
  input   rst,
  // pipe controls
  input   pipeline_flush_i,
  input   take_op_fp32_arith_i,  // write: an FPU pipe is taking operands
  input   rnd_taking_op_i,       // read:  rounding engine is taking result
  // data input
  input   add_start_i,
  input   mul_start_i,
  input   i2f_start_i,
  input   f2i_start_i,
  // data ouputs
  output  grant_rnd_to_add_o,
  output  grant_rnd_to_mul_o,
  output  grant_rnd_to_i2f_o,
  output  grant_rnd_to_f2i_o,
  // "OCB is full" flag
  //   (a) external control logic must stop the "writing without reading"
  //       operation if OCB is full
  //   (b) however, the "writing + reading" is possible
  //       because it just pushes OCB and keeps it full
  output  pfpu32_ocb_full_o
);

  localparam NUM_TAPS = 4;

  // "pointers"
  reg   [NUM_TAPS:0] ptr_curr; // on current active tap
  reg [NUM_TAPS-1:0] ptr_prev; // on previous active tap

  // pointers are zero: tap #0 (output) is active
  wire ptr_curr_0 = ptr_curr[0];
  wire ptr_prev_0 = ptr_prev[0];

  // "OCB is full" flag
  //  # no more availaible taps, pointer is out of range
  assign pfpu32_ocb_full_o = ptr_curr[NUM_TAPS];

  // control to increment/decrement pointers
  wire rd_only = ~take_op_fp32_arith_i &  rnd_taking_op_i;
  wire wr_only =  take_op_fp32_arith_i & ~rnd_taking_op_i;
  wire wr_rd   =  take_op_fp32_arith_i &  rnd_taking_op_i;


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
  end // posedge clock

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
  end // posedge clock


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
  wire [3:0] ocbi = {add_start_i, mul_start_i, i2f_start_i, f2i_start_i};

  // taps ouputs
  wire [3:0] ocbo00; // OCB output
  wire [3:0] ocbo01; // ...
  wire [3:0] ocbo02; // ...
  wire [3:0] ocbo03; // OCB entrance

  // granting flags output
  assign {grant_rnd_to_add_o, grant_rnd_to_mul_o, grant_rnd_to_i2f_o, grant_rnd_to_f2i_o} = ocbo00;

  // taps
  //   tap #00
  ocb_tap
  #(
    .DATA_SIZE (4)
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
    .DATA_SIZE (4)
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
    .DATA_SIZE (4)
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
    .DATA_SIZE (4)
  )
  u_tap_03
  (
    .clk                    (clk),
    .rst                    (rst),
    .flush_i                (pipeline_flush_i),
    .push_i                 (push_taps[3]),
    .prev_tap_out_i         (4'd0),
    .forwarded_value_i      (ocbi),
    .use_forwarded_value_i  (use_forwarded_value[3]),
    .out_o                  (ocbo03)
  );
endmodule // pfpu32_ocb_marocchino


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


module pfpu32_top_marocchino
#(
  parameter DEST_REG_ADDR_WIDTH  =  8 // OPTION_RF_ADDR_WIDTH + log2(Re-Ordering buffer width)
)
(
  // clock & reset
  input                             clk,
  input                             rst,

  // pipeline control
  input                             pipeline_flush_i,
  input                             padv_decode_i,
  input                             padv_wb_i,
  input                             grant_wb_to_fp32_arith_i,

  // pipeline control outputs
  output                            fp32_arith_busy_o,     // idicates that arihmetic units are busy
  output                            fp32_arith_valid_o,    // WB-latching ahead arithmetic ready flag

  // Configuration
  input   [`OR1K_FPCSR_RM_SIZE-1:0] round_mode_i,
  input                             except_fpu_enable_i,
  input [`OR1K_FPCSR_ALLF_SIZE-1:0] ctrl_fpu_mask_flags_i,

  // Operands and commands
  input                             dcod_op_fp32_arith_i,
  input                             dcod_op_fp32_add_i,
  input                             dcod_op_fp32_sub_i,
  input                             dcod_op_fp32_mul_i,
  input                             dcod_op_fp32_div_i,
  input                             dcod_op_fp32_i2f_i,
  input                             dcod_op_fp32_f2i_i,
  //   from DECODE
  input                      [31:0] dcod_rfa_i,
  input                      [31:0] dcod_rfb_i,

  // OMAN-to-DECODE hazards
  //  combined flag
  input                             omn2dec_hazards_i,
  //  by operands
  input                             busy_hazard_a_i,
  input   [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_a_adr_i,
  input                             busy_hazard_b_i,
  input   [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_b_adr_i,

  // EXEC-to-DECODE hazards
  //  combined flag
  input                             exe2dec_hazards_i,
  //  by operands
  input                             exe2dec_hazard_a_i,
  input                             exe2dec_hazard_b_i,

  // Data for hazards resolving
  //  hazard could be passed from DECODE to EXECUTE
  input                             exec_rf_wb_i,
  input   [DEST_REG_ADDR_WIDTH-1:0] exec_rfd_adr_i,
  //  hazard could be resolving
  input                             wb_rf_wb_i,
  input   [DEST_REG_ADDR_WIDTH-1:0] wb_rfd_adr_i,
  input                      [31:0] wb_result_i,

  // FPU-32 arithmetic part
  output                      [31:0] wb_fp32_arith_res_o,      // arithmetic result
  output [`OR1K_FPCSR_ALLF_SIZE-1:0] wb_fp32_arith_fpcsr_o,    // arithmetic exceptions
  output                             wb_fp32_arith_wb_fpcsr_o, // update FPCSR
  output                             wb_except_fp32_arith_o    // generate exception

);

// fp32 arithmetic command
wire exec_op_fp32_add, exec_op_fp32_sub, exec_op_fp32_mul,
     exec_op_fp32_div, exec_op_fp32_i2f, exec_op_fp32_f2i;

// fp32 pipes controls
wire        take_op_fp32_arith;

// operand A and B  with forwarding from WB
wire [31:0] fp32_arith_a;
wire [31:0] fp32_arith_b;

// reservation station instance
mor1kx_rsrvs_marocchino
#(
  .OPTION_OPERAND_WIDTH     (32), // FP32_ARITH_RSVRS
  .USE_OPC                  (1), // FP32_ARITH_RSVRS
  .OPC_WIDTH                (6), // FP32_ARITH_RSVRS
  .DEST_REG_ADDR_WIDTH      (DEST_REG_ADDR_WIDTH), // FP32_ARITH_RSVRS
  .USE_RSVRS_FLAG_CARRY     (0), // FP32_ARITH_RSVRS
  .DEST_FLAG_ADDR_WIDTH     (1) // FP32_ARITH_RSVRS
)
u_fp32_arith_rsrvs
(
  // clocks and resets
  .clk                      (clk),
  .rst                      (rst),
  // pipeline control signals in
  .pipeline_flush_i         (pipeline_flush_i), // FP32_ARITH_RSVRS
  .padv_decode_i            (padv_decode_i), // FP32_ARITH_RSVRS
  .taking_op_i              (take_op_fp32_arith), // FP32_ARITH_RSVRS
  // input data from DECODE
  .dcod_rfa_i               (dcod_rfa_i), // FP32_ARITH_RSVRS
  .dcod_rfb_i               (dcod_rfb_i), // FP32_ARITH_RSVRS
  // OMAN-to-DECODE hazards
  //  combined flag
  .omn2dec_hazards_i        (omn2dec_hazards_i), // FP32_ARITH_RSVRS
  //  by FLAG and CARRY
  .busy_hazard_f_i          (1'b0), // FP32_ARITH_RSVRS
  .busy_hazard_f_adr_i      (1'b0), // FP32_ARITH_RSVRS
  .busy_hazard_c_i          (1'b0), // FP32_ARITH_RSVRS
  .busy_hazard_c_adr_i      (1'b0), // FP32_ARITH_RSVRS
  //  by operands
  .busy_hazard_a_i          (busy_hazard_a_i), // FP32_ARITH_RSVRS
  .busy_hazard_a_adr_i      (busy_hazard_a_adr_i), // FP32_ARITH_RSVRS
  .busy_hazard_b_i          (busy_hazard_b_i), // FP32_ARITH_RSVRS
  .busy_hazard_b_adr_i      (busy_hazard_b_adr_i), // FP32_ARITH_RSVRS
  // EXEC-to-DECODE hazards
  //  combined flag
  .exe2dec_hazards_i        (exe2dec_hazards_i), // FP32_ARITH_RSVRS
  //  by operands
  .exe2dec_hazard_a_i       (exe2dec_hazard_a_i), // FP32_ARITH_RSVRS
  .exe2dec_hazard_b_i       (exe2dec_hazard_b_i), // FP32_ARITH_RSVRS
  // Data for hazards resolving
  //  hazard could be passed from DECODE to EXECUTE
  .exec_flag_wb_i           (1'b0), // FP32_ARITH_RSVRS
  .exec_carry_wb_i          (1'b0), // FP32_ARITH_RSVRS
  .exec_flag_carry_adr_i    (1'b0), // FP32_ARITH_RSVRS
  .exec_rf_wb_i             (exec_rf_wb_i), // FP32_ARITH_RSVRS
  .exec_rfd_adr_i           (exec_rfd_adr_i), // FP32_ARITH_RSVRS
  .padv_wb_i                (padv_wb_i), // FP32_ARITH_RSVRS
  //  hazard could be resolving
  .wb_flag_wb_i             (1'b0), // FP32_ARITH_RSVRS
  .wb_carry_wb_i            (1'b0), // FP32_ARITH_RSVRS
  .wb_flag_carry_adr_i      (1'b0), // FP32_ARITH_RSVRS
  .wb_rf_wb_i               (wb_rf_wb_i), // FP32_ARITH_RSVRS
  .wb_rfd_adr_i             (wb_rfd_adr_i), // FP32_ARITH_RSVRS
  .wb_result_i              (wb_result_i), // FP32_ARITH_RSVRS
  // command and its additional attributes
  .dcod_op_i                (dcod_op_fp32_arith_i), // FP32_ARITH_RSVRS
  .dcod_opc_i               ({dcod_op_fp32_add_i, dcod_op_fp32_sub_i, dcod_op_fp32_mul_i, // FP32_ARITH_RSVRS
                              dcod_op_fp32_div_i, dcod_op_fp32_i2f_i, dcod_op_fp32_f2i_i}), // FP32_ARITH_RSVRS
  // outputs
  //   command attributes from busy stage
  .busy_opc_o               (), // FP32_ARITH_RSVRS
  //   command and its additional attributes
  .exec_op_o                (), // FP32_ARITH_RSVRS
  .exec_opc_o               ({exec_op_fp32_add, exec_op_fp32_sub, exec_op_fp32_mul, // FP32_ARITH_RSVRS
                              exec_op_fp32_div, exec_op_fp32_i2f, exec_op_fp32_f2i}), // FP32_ARITH_RSVRS
  //   operands
  .exec_rfa_o               (fp32_arith_a), // FP32_ARITH_RSVRS
  .exec_rfb_o               (fp32_arith_b), // FP32_ARITH_RSVRS
  //   unit-is-busy flag
  .unit_busy_o              (fp32_arith_busy_o) // FP32_ARITH_RSVRS
);

// analysis of input values
//   split input a
wire        in_signa  = fp32_arith_a[31];
wire [7:0]  in_expa   = fp32_arith_a[30:23];
wire [22:0] in_fracta = fp32_arith_a[22:0];
//   detect infinity a
wire in_expa_ff = &in_expa;
wire in_infa    = in_expa_ff & (~(|in_fracta));
//   signaling NaN: exponent is 8hff, [22] is zero,
//                  rest of fract is non-zero
//   quiet NaN: exponent is 8hff, [22] is 1
wire in_snan_a = in_expa_ff & (~in_fracta[22]) & (|in_fracta[21:0]);
wire in_qnan_a = in_expa_ff &   in_fracta[22];
//   denormalized/zero of a
wire in_opa_0  = ~(|fp32_arith_a[30:0]);
wire in_opa_dn = (~(|in_expa)) & (|in_fracta);

//   split input b
wire        in_signb  = fp32_arith_b[31];
wire [7:0]  in_expb   = fp32_arith_b[30:23];
wire [22:0] in_fractb = fp32_arith_b[22:0];
//   detect infinity b
wire in_expb_ff = &in_expb;
wire in_infb    = in_expb_ff & (~(|in_fractb));
//   detect NaNs in b
wire in_snan_b = in_expb_ff & (~in_fractb[22]) & (|in_fractb[21:0]);
wire in_qnan_b = in_expb_ff &   in_fractb[22];
//   denormalized/zero of a
wire in_opb_0  = ~(|fp32_arith_b[30:0]);
wire in_opb_dn = (~(|in_expb)) & (|in_fractb);

// detection of some exceptions
//   a nan input -> qnan output
wire in_snan = in_snan_a | in_snan_b;
wire in_qnan = in_qnan_a | in_qnan_b;
//   sign of output nan
wire in_anan_sign = (in_snan_a | in_qnan_a) ? in_signa :
                                              in_signb;

// restored exponents
wire [9:0] in_exp10a = {2'd0,in_expa[7:1],(in_expa[0] | in_opa_dn)};
wire [9:0] in_exp10b = {2'd0,in_expb[7:1],(in_expb[0] | in_opb_dn)};
// restored fractionals
wire [23:0] in_fract24a = {((~in_opa_dn) & (~in_opa_0)),in_fracta};
wire [23:0] in_fract24b = {((~in_opb_dn) & (~in_opb_0)),in_fractb};


// Support for ADD/SUB (historically they were comparator's part)
//  # exponents
wire exp_gt = in_exp10a  > in_exp10b;
wire exp_eq = in_exp10a == in_exp10b;
//  # fractionals
wire fract_gt = in_fract24a  > in_fract24b;
wire fract_eq = in_fract24a == in_fract24b;
//  # comparisons for ADD/SUB
wire addsub_agtb = exp_gt | (exp_eq & fract_gt);
wire addsub_aeqb = exp_eq & fract_eq;


// order control buffer is full:
// we are waiting an arithmetic pipe result for rounding
wire pfpu32_ocb_full;

// unit-wise control signals
//  ## ADD / SUB
wire op_add             = exec_op_fp32_add & (~pfpu32_ocb_full);
wire op_sub             = exec_op_fp32_sub & (~pfpu32_ocb_full);
wire add_start          = op_add | op_sub;
wire add_takes_op;
wire add_rdy;
wire grant_rnd_to_add;
wire rnd_muxing_add     = add_rdy & grant_rnd_to_add; // to rounding input muxer
wire rnd_taking_add;
//  ## MUL/DIV
wire op_mul             = exec_op_fp32_mul & (~pfpu32_ocb_full);
wire op_div             = exec_op_fp32_div & (~pfpu32_ocb_full);
wire mul_start          = op_mul | op_div;
wire muldiv_takes_op;
wire muldiv_rdy;
wire grant_rnd_to_mul;
wire rnd_muxing_muldiv  = muldiv_rdy & grant_rnd_to_mul; // to rounding input muxer
wire rnd_taking_muldiv;
//  ## i2f
wire i2f_start          = exec_op_fp32_i2f & (~pfpu32_ocb_full);
wire i2f_takes_op;
wire i2f_rdy;
wire grant_rnd_to_i2f;
wire rnd_muxing_i2f     = i2f_rdy & grant_rnd_to_i2f; // to rounding input muxer
wire rnd_taking_i2f;
//  ## f2i
wire f2i_start          = exec_op_fp32_f2i & (~pfpu32_ocb_full);
wire f2i_takes_op;
wire f2i_rdy;
wire grant_rnd_to_f2i;
wire rnd_muxing_f2i     = f2i_rdy & grant_rnd_to_f2i; // to rounding input muxer
wire rnd_taking_f2i;

// feedback to drop FP32 arithmetic related command
assign take_op_fp32_arith = add_takes_op | muldiv_takes_op | i2f_takes_op | f2i_takes_op;

// rounding engine takes an OP
wire rnd_taking_op = rnd_taking_add | rnd_taking_muldiv | rnd_taking_i2f | rnd_taking_f2i;


// ---
pfpu32_ocb_marocchino  u_pfpu32_ocb
(
  // clocks and resets
  .clk                    (clk), // PFPU32_OCB
  .rst                    (rst), // PFPU32_OCB
  // pipe controls
  .pipeline_flush_i       (pipeline_flush_i), // PFPU32_OCB
  .take_op_fp32_arith_i   (take_op_fp32_arith), // PFPU32_OCB
  .rnd_taking_op_i        (rnd_taking_op), // PFPU32_OCB
  // data input
  .add_start_i            (add_start), // PFPU32_OCB
  .mul_start_i            (mul_start), // PFPU32_OCB
  .i2f_start_i            (i2f_start), // PFPU32_OCB
  .f2i_start_i            (f2i_start), // PFPU32_OCB
  // data ouputs
  .grant_rnd_to_add_o     (grant_rnd_to_add), // PFPU32_OCB
  .grant_rnd_to_mul_o     (grant_rnd_to_mul), // PFPU32_OCB
  .grant_rnd_to_i2f_o     (grant_rnd_to_i2f), // PFPU32_OCB
  .grant_rnd_to_f2i_o     (grant_rnd_to_f2i), // PFPU32_OCB
  // "OCB is full" flag
  .pfpu32_ocb_full_o      (pfpu32_ocb_full) // PFPU32_OCB
);


// Addition / Substruction
//   connection wires
wire        add_sign;      // add/sub signum
wire        add_sub_0;     // flag that actual substruction is performed and result is zero
wire  [4:0] add_shl;       // do left shift in align stage
wire  [9:0] add_exp10shl;  // exponent for left shift align
wire  [9:0] add_exp10sh0;  // exponent for no shift in align
wire [27:0] add_fract28;   // fractional with appended {r,s} bits
wire        add_inv;       // add/sub invalid operation flag
wire        add_inf;       // add/sub infinity output reg
wire        add_snan;      // add/sub signaling NaN output reg
wire        add_qnan;      // add/sub quiet NaN output reg
wire        add_anan_sign; // add/sub signum for output nan
//   module istance
pfpu32_addsub_marocchino u_f32_addsub
(
  // clocks and resets
  .clk              (clk), // FP32_ADDSUB
  .rst              (rst), // FP32_ADDSUB
  // ADD/SUB pipe controls
  .pipeline_flush_i (pipeline_flush_i), // FP32_ADDSUB
  .start_i          (add_start), // FP32_ADDSUB 
  .is_sub_i         (op_sub), // FP32_ADDSUB
  .add_takes_op_o   (add_takes_op), // FP32_ADDSUB
  .add_rdy_o        (add_rdy), // FP32_ADDSUB
  .rnd_taking_add_i (rnd_taking_add), // FP32_ADDSUB
  // input 'a' related values
  .signa_i          (in_signa), // FP32_ADDSUB
  .exp10a_i         (in_exp10a), // FP32_ADDSUB
  .fract24a_i       (in_fract24a), // FP32_ADDSUB
  .infa_i           (in_infa), // FP32_ADDSUB
  // input 'b' related values
  .signb_i          (in_signb), // FP32_ADDSUB
  .exp10b_i         (in_exp10b), // FP32_ADDSUB
  .fract24b_i       (in_fract24b), // FP32_ADDSUB
  .infb_i           (in_infb), // FP32_ADDSUB
  // 'a'/'b' related
  .snan_i           (in_snan), // FP32_ADDSUB
  .qnan_i           (in_qnan), // FP32_ADDSUB
  .anan_sign_i      (in_anan_sign), // FP32_ADDSUB
  .addsub_agtb_i    (addsub_agtb), // FP32_ADDSUB
  .addsub_aeqb_i    (addsub_aeqb), // FP32_ADDSUB
  // outputs
  .add_sign_o       (add_sign), // FP32_ADDSUB
  .add_sub_0_o      (add_sub_0), // FP32_ADDSUB
  .add_shl_o        (add_shl), // FP32_ADDSUB
  .add_exp10shl_o   (add_exp10shl), // FP32_ADDSUB
  .add_exp10sh0_o   (add_exp10sh0), // FP32_ADDSUB
  .add_fract28_o    (add_fract28), // FP32_ADDSUB
  .add_inv_o        (add_inv), // FP32_ADDSUB
  .add_inf_o        (add_inf), // FP32_ADDSUB
  .add_snan_o       (add_snan), // FP32_ADDSUB
  .add_qnan_o       (add_qnan), // FP32_ADDSUB
  .add_anan_sign_o  (add_anan_sign) // FP32_ADDSUB
);

// MUL/DIV combined pipeline
//   MUL/DIV common outputs
wire        mul_sign;      // mul signum
wire  [4:0] mul_shr;       // do right shift in align stage
wire  [9:0] mul_exp10shr;  // exponent for right shift align
wire        mul_shl;       // do left shift in align stage
wire  [9:0] mul_exp10shl;  // exponent for left shift align
wire  [9:0] mul_exp10sh0;  // exponent for no shift in align
wire [27:0] mul_fract28;   // fractional with appended {r,s} bits
wire        mul_inv;       // mul invalid operation flag
wire        mul_inf;       // mul infinity output reg
wire        mul_snan;      // mul signaling NaN output reg
wire        mul_qnan;      // mul quiet NaN output reg
wire        mul_anan_sign; // mul signum for output nan
//   DIV additional outputs
wire        div_op;        // operation is division
wire        div_sign_rmnd; // signum or reminder for IEEE compliant rounding
wire        div_dbz;       // division by zero flag
//   module istance
pfpu32_muldiv_marocchino u_f32_muldiv
(
  // clocks and resets
  .clk                  (clk), // FP32_MULDIV
  .rst                  (rst), // FP32_MULDIV
  // pipe controls
  .pipeline_flush_i     (pipeline_flush_i), // FP32_MULDIV
  .is_mul_i             (op_mul), // FP32_MULDIV
  .is_div_i             (op_div), // FP32_MULDIV
  .muldiv_takes_op_o    (muldiv_takes_op), // FP32_MULDIV
  .muldiv_rdy_o         (muldiv_rdy), // FP32_MULDIV
  .rnd_taking_muldiv_i  (rnd_taking_muldiv), // FP32_MULDIV
  // input 'a' related values
  .signa_i              (in_signa), // FP32_MULDIV
  .exp10a_i             (in_exp10a), // FP32_MULDIV
  .fract24a_i           (in_fract24a), // FP32_MULDIV
  .infa_i               (in_infa), // FP32_MULDIV
  .zeroa_i              (in_opa_0), // FP32_MULDIV
  // input 'b' related values
  .signb_i              (in_signb), // FP32_MULDIV
  .exp10b_i             (in_exp10b), // FP32_MULDIV
  .fract24b_i           (in_fract24b), // FP32_MULDIV
  .infb_i               (in_infb), // FP32_MULDIV
  .zerob_i              (in_opb_0), // FP32_MULDIV
  // 'a'/'b' related
  .snan_i               (in_snan), // FP32_MULDIV       
  .qnan_i               (in_qnan), // FP32_MULDIV
  .anan_sign_i          (in_anan_sign), // FP32_MULDIV
  // MUL/DIV common outputs
  .muldiv_sign_o        (mul_sign), // FP32_MULDIV
  .muldiv_shr_o         (mul_shr), // FP32_MULDIV
  .muldiv_exp10shr_o    (mul_exp10shr), // FP32_MULDIV
  .muldiv_shl_o         (mul_shl), // FP32_MULDIV
  .muldiv_exp10shl_o    (mul_exp10shl), // FP32_MULDIV
  .muldiv_exp10sh0_o    (mul_exp10sh0), // FP32_MULDIV
  .muldiv_fract28_o     (mul_fract28), // FP32_MULDIV
  .muldiv_inv_o         (mul_inv), // FP32_MULDIV
  .muldiv_inf_o         (mul_inf), // FP32_MULDIV
  .muldiv_snan_o        (mul_snan), // FP32_MULDIV
  .muldiv_qnan_o        (mul_qnan), // FP32_MULDIV
  .muldiv_anan_sign_o   (mul_anan_sign), // FP32_MULDIV
  // DIV additional outputs
  .div_op_o             (div_op), // FP32_MULDIV
  .div_sign_rmnd_o      (div_sign_rmnd), // FP32_MULDIV
  .div_dbz_o            (div_dbz) // FP32_MULDIV
);

// convertors
//   i2f connection wires
wire        i2f_sign;
wire  [3:0] i2f_shr;
wire  [7:0] i2f_exp8shr;
wire  [4:0] i2f_shl;
wire  [7:0] i2f_exp8shl;
wire  [7:0] i2f_exp8sh0;
wire [31:0] i2f_fract32;
//   i2f module instance
pfpu32_i2f_marocchino u_i2f_cnv
(
  // clocks and resets
  .clk                (clk), // FP32_I2F
  .rst                (rst), // FP32_I2F
  // I2F pipe controls
  .pipeline_flush_i   (pipeline_flush_i), // FP32_I2F
  .start_i            (i2f_start), // FP32_I2F
  .i2f_takes_op_o     (i2f_takes_op), // FP32_I2F
  .i2f_rdy_o          (i2f_rdy), // FP32_I2F
  .rnd_taking_i2f_i   (rnd_taking_i2f), // FP32_I2F
  // operand for conversion
  .opa_i              (fp32_arith_a), // FP32_I2F
  // ouputs for rounding
  .i2f_sign_o         (i2f_sign), // FP32_I2F
  .i2f_shr_o          (i2f_shr), // FP32_I2F
  .i2f_exp8shr_o      (i2f_exp8shr), // FP32_I2F
  .i2f_shl_o          (i2f_shl), // FP32_I2F
  .i2f_exp8shl_o      (i2f_exp8shl), // FP32_I2F
  .i2f_exp8sh0_o      (i2f_exp8sh0), // FP32_I2F
  .i2f_fract32_o      (i2f_fract32) // FP32_I2F
);
//   f2i connection wires
wire        f2i_sign;      // f2i signum
wire [23:0] f2i_int24;     // f2i fractional
wire  [4:0] f2i_shr;       // f2i required shift right value
wire  [3:0] f2i_shl;       // f2i required shift left value   
wire        f2i_ovf;       // f2i overflow flag
wire        f2i_snan;      // f2i signaling NaN output reg
//    f2i module instance
pfpu32_f2i_marocchino u_f2i_cnv
(
  // clocks and resets
  .clk                  (clk), // FP32_F2I
  .rst                  (rst), // FP32_F2I
  // pipe controls
  .pipeline_flush_i     (pipeline_flush_i), // FP32_F2I
  .start_i              (f2i_start), // FP32_F2I
  .f2i_takes_op_o       (f2i_takes_op), // FP32_F2I
  .f2i_rdy_o            (f2i_rdy), // FP32_F2I
  .rnd_taking_f2i_i     (rnd_taking_f2i), // FP32_F2I
  // input data
  .signa_i              (in_signa), // FP32_F2I
  .exp10a_i             (in_exp10a), // FP32_F2I
  .fract24a_i           (in_fract24a), // FP32_F2I
  .snan_i               (in_snan), // FP32_F2I
  .qnan_i               (in_qnan), // FP32_F2I
  // output data for rounding
  .f2i_sign_o           (f2i_sign), // FP32_F2I
  .f2i_int24_o          (f2i_int24), // FP32_F2I
  .f2i_shr_o            (f2i_shr), // FP32_F2I
  .f2i_shl_o            (f2i_shl), // FP32_F2I  
  .f2i_ovf_o            (f2i_ovf), // FP32_F2I
  .f2i_snan_o           (f2i_snan) // FP32_F2I
);


// multiplexing and rounding
pfpu32_rnd_marocchino u_f32_rnd
(
  // clocks, resets
  .clk                      (clk), // FP32_RND
  .rst                      (rst), // FP32_RND
  // pipe controls
  .pipeline_flush_i         (pipeline_flush_i), // FP32_RND
  .rnd_taking_add_o         (rnd_taking_add), // FP32_RND
  .rnd_taking_mul_o         (rnd_taking_muldiv), // FP32_RND
  .rnd_taking_i2f_o         (rnd_taking_i2f), // FP32_RND
  .rnd_taking_f2i_o         (rnd_taking_f2i), // FP32_RND
  .fp32_arith_valid_o       (fp32_arith_valid_o), // FP32_RND
  .padv_wb_i                (padv_wb_i), // FP32_RND
  .grant_wb_to_fp32_arith_i (grant_wb_to_fp32_arith_i), // FP32_RND
  // configuration
  .rmode_i                  (round_mode_i), // FP32_RND
  .except_fpu_enable_i      (except_fpu_enable_i), // FP32_RND
  .ctrl_fpu_mask_flags_i    (ctrl_fpu_mask_flags_i), // FP32_RND
  // from add/sub
  .add_rdy_i       (rnd_muxing_add), // FP32_RND
  .add_sign_i      (add_sign), // FP32_RND
  .add_sub_0_i     (add_sub_0), // FP32_RND
  .add_shl_i       (add_shl), // FP32_RND
  .add_exp10shl_i  (add_exp10shl), // FP32_RND
  .add_exp10sh0_i  (add_exp10sh0), // FP32_RND
  .add_fract28_i   (add_fract28), // FP32_RND
  .add_inv_i       (add_inv), // FP32_RND
  .add_inf_i       (add_inf), // FP32_RND
  .add_snan_i      (add_snan), // FP32_RND
  .add_qnan_i      (add_qnan), // FP32_RND
  .add_anan_sign_i (add_anan_sign), // FP32_RND
  // from mul
  .mul_rdy_i       (rnd_muxing_muldiv), // FP32_RND
  .mul_sign_i      (mul_sign), // FP32_RND
  .mul_shr_i       (mul_shr), // FP32_RND
  .mul_exp10shr_i  (mul_exp10shr), // FP32_RND
  .mul_shl_i       (mul_shl), // FP32_RND
  .mul_exp10shl_i  (mul_exp10shl), // FP32_RND
  .mul_exp10sh0_i  (mul_exp10sh0), // FP32_RND
  .mul_fract28_i   (mul_fract28), // FP32_RND
  .mul_inv_i       (mul_inv), // FP32_RND
  .mul_inf_i       (mul_inf), // FP32_RND
  .mul_snan_i      (mul_snan), // FP32_RND
  .mul_qnan_i      (mul_qnan), // FP32_RND
  .mul_anan_sign_i (mul_anan_sign), // FP32_RND
  .div_op_i        (div_op), // FP32_RND
  .div_sign_rmnd_i (div_sign_rmnd), // FP32_RND
  .div_dbz_i       (div_dbz), // FP32_RND
  // from i2f
  .i2f_rdy_i       (rnd_muxing_i2f), // FP32_RND
  .i2f_sign_i      (i2f_sign), // FP32_RND
  .i2f_shr_i       (i2f_shr), // FP32_RND
  .i2f_exp8shr_i   (i2f_exp8shr), // FP32_RND
  .i2f_shl_i       (i2f_shl), // FP32_RND
  .i2f_exp8shl_i   (i2f_exp8shl), // FP32_RND
  .i2f_exp8sh0_i   (i2f_exp8sh0), // FP32_RND
  .i2f_fract32_i   (i2f_fract32), // FP32_RND
  // from f2i
  .f2i_rdy_i       (rnd_muxing_f2i), // FP32_RND
  .f2i_sign_i      (f2i_sign), // FP32_RND
  .f2i_int24_i     (f2i_int24), // FP32_RND
  .f2i_shr_i       (f2i_shr), // FP32_RND
  .f2i_shl_i       (f2i_shl), // FP32_RND  
  .f2i_ovf_i       (f2i_ovf), // FP32_RND
  .f2i_snan_i      (f2i_snan), // FP32_RND
  // output WB latches
  .wb_fp32_arith_res_o      (wb_fp32_arith_res_o), // FP32_RND
  .wb_fp32_arith_fpcsr_o    (wb_fp32_arith_fpcsr_o), // FP32_RND
  .wb_fp32_arith_wb_fpcsr_o (wb_fp32_arith_wb_fpcsr_o), // FP32_RND
  .wb_except_fp32_arith_o   (wb_except_fp32_arith_o) // FP32_RND
);

endmodule // pfpu32_top_marocchino
