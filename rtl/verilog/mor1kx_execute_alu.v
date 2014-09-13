/* ****************************************************************************
  This Source Code Form is subject to the terms of the
  Open Hardware Description License, v. 1.0. If a copy
  of the OHDL was not distributed with this file, You
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: mor1kx execute stage ALU

  Inputs are opcodes, the immediate field, operands from RF, instruction
  opcode

   Copyright (C) 2012 Authors

  Author(s): Julius Baxter <juliusbaxter@gmail.com>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_execute_alu
  #(
    parameter OPTION_OPERAND_WIDTH = 32,

    parameter FEATURE_MULTIPLIER = "THREESTAGE",
    parameter FEATURE_DIVIDER = "NONE",

    parameter FEATURE_ADDC = "NONE",
    parameter FEATURE_SRA = "ENABLED",
    parameter FEATURE_ROR = "NONE",
    parameter FEATURE_EXT = "NONE",
    parameter FEATURE_CMOV = "NONE",
    parameter FEATURE_FFL1 = "NONE",

    parameter FEATURE_CUST1 = "NONE",
    parameter FEATURE_CUST2 = "NONE",
    parameter FEATURE_CUST3 = "NONE",
    parameter FEATURE_CUST4 = "NONE",
    parameter FEATURE_CUST5 = "NONE",
    parameter FEATURE_CUST6 = "NONE",
    parameter FEATURE_CUST7 = "NONE",
    parameter FEATURE_CUST8 = "NONE",

    parameter FEATURE_FPU   = "NONE", // ENABLED|NONE

    parameter OPTION_SHIFTER = "BARREL",

    // Pipeline specific internal parameters
    parameter CALCULATE_BRANCH_DEST = "TRUE"
    )
   (
    input 			      clk,
    input 			      rst,

    // pipeline control signal in
    input 			      padv_execute_i,
    input 			      padv_ctrl_i,

    // inputs to ALU
    input [`OR1K_ALU_OPC_WIDTH-1:0]   opc_alu_i,
    input [`OR1K_ALU_OPC_WIDTH-1:0]   opc_alu_secondary_i,

    input [`OR1K_IMM_WIDTH-1:0]       imm16_i,
    input [OPTION_OPERAND_WIDTH-1:0]  immediate_i,
    input 			      immediate_sel_i,

    input 			      decode_valid_i,

    input 			      op_alu_i,
    input 			      op_add_i,
    input 			      op_mul_i,
    input 			      op_mul_signed_i,
    input 			      op_mul_unsigned_i,
    input 			      op_div_i,
    input 			      op_div_signed_i,
    input 			      op_div_unsigned_i,
    input 			      op_shift_i,
    input 			      op_ffl1_i,
    input 			      op_setflag_i,
    input 			      op_mtspr_i,
    input 			      op_mfspr_i,
    input 			      op_movhi_i,
    input [`OR1K_FPUOP_WIDTH-1:0]   op_fpu_i,
    input [`OR1K_FPCSR_RM_SIZE-1:0] fpu_round_mode_i,
    input 			      op_jbr_i,
    input 			      op_jr_i,
    input [9:0] 		      immjbr_upper_i,
    input [OPTION_OPERAND_WIDTH-1:0]  pc_execute_i,

    // Adder control logic
    input 			      adder_do_sub_i,
    input 			      adder_do_carry_i,

    input [OPTION_OPERAND_WIDTH-1:0]  rfa_i,
    input [OPTION_OPERAND_WIDTH-1:0]  rfb_i,

    // flag fed back from ctrl
    input 			      flag_i,

    output 			      flag_set_o,
    output 			      flag_clear_o,

    input 			      carry_i,
    output 			      carry_set_o,
    output 			      carry_clear_o,

    output 			      overflow_set_o,
    output 			      overflow_clear_o,

    output [`OR1K_FPCSR_WIDTH-1:0] fpcsr_o,
    output                         fpcsr_set_o,

    output [OPTION_OPERAND_WIDTH-1:0] alu_result_o,
    output 			      alu_valid_o,
    output [OPTION_OPERAND_WIDTH-1:0] mul_result_o,
    output [OPTION_OPERAND_WIDTH-1:0] adder_result_o
    );

   wire                                   alu_stall;

   wire [OPTION_OPERAND_WIDTH-1:0]        a;
   wire [OPTION_OPERAND_WIDTH-1:0]        b;

   // Adder & comparator wires
   wire [OPTION_OPERAND_WIDTH-1:0]        adder_result;
   wire                                   adder_carryout;
   wire 				  adder_signed_overflow;
   wire 				  adder_unsigned_overflow;
   wire 				  adder_result_sign;

   wire [OPTION_OPERAND_WIDTH-1:0]        b_neg;
   wire [OPTION_OPERAND_WIDTH-1:0]        b_mux;
   wire                                   carry_in;

   wire                                   a_eq_b;
   wire                                   a_lts_b;
   wire                                   a_ltu_b;

   // Shifter wires
   wire [`OR1K_ALU_OPC_SECONDARY_WIDTH-1:0] opc_alu_shr;
   wire [OPTION_OPERAND_WIDTH-1:0]        shift_result;
   wire                                   shift_valid;

   // Comparison wires
   reg                                    flag_set; // comb.

   // Logic wires
   wire 				  op_and;
   wire 				  op_or;
   wire 				  op_xor;
   wire [OPTION_OPERAND_WIDTH-1:0]        and_result;
   wire [OPTION_OPERAND_WIDTH-1:0]        or_result;
   wire [OPTION_OPERAND_WIDTH-1:0]        xor_result;

   // Multiplier wires
   wire [OPTION_OPERAND_WIDTH-1:0]        mul_result;
   wire                                   mul_valid;
   wire 				  mul_signed_overflow;
   wire 				  mul_unsigned_overflow;

   wire [OPTION_OPERAND_WIDTH-1:0]        div_result;
   wire                                   div_valid;
   wire 				  div_by_zero;


   wire [OPTION_OPERAND_WIDTH-1:0]        ffl1_result;

   wire 				  op_cmov;
   wire [OPTION_OPERAND_WIDTH-1:0]        cmov_result;

generate
if (CALCULATE_BRANCH_DEST=="TRUE") begin : calculate_branch_dest
   assign a = (op_jbr_i | op_jr_i) ? pc_execute_i : rfa_i;
   assign b = immediate_sel_i ? immediate_i :
              op_jbr_i ? {{4{immjbr_upper_i[9]}},immjbr_upper_i,imm16_i,2'b00} :
              rfb_i;
end else begin
   assign a = rfa_i;
   assign b = immediate_sel_i ? immediate_i : rfb_i;
end
endgenerate

   assign opc_alu_shr = opc_alu_secondary_i[`OR1K_ALU_OPC_SECONDARY_WIDTH-1:0];

   // Adder/subtractor inputs
   assign b_neg = ~b;
   assign carry_in = adder_do_sub_i | adder_do_carry_i & carry_i;
   assign b_mux = adder_do_sub_i ? b_neg : b;
   // Adder
   assign {adder_carryout, adder_result} = a + b_mux +
                                           {{OPTION_OPERAND_WIDTH-1{1'b0}},
                                            carry_in};

   assign adder_result_sign = adder_result[OPTION_OPERAND_WIDTH-1];

   assign adder_signed_overflow = // Input signs are same and ...
				  (a[OPTION_OPERAND_WIDTH-1] ==
				   b_mux[OPTION_OPERAND_WIDTH-1]) &
				  // result sign is different to input signs
				  (a[OPTION_OPERAND_WIDTH-1] ^
				   adder_result[OPTION_OPERAND_WIDTH-1]);

   assign adder_unsigned_overflow = adder_carryout;

   assign adder_result_o = adder_result;

   generate
      /* verilator lint_off WIDTH */
      if (FEATURE_MULTIPLIER=="THREESTAGE") begin : threestagemultiply
	 /* verilator lint_on WIDTH */
         // 32-bit multiplier with three registering stages to help with timing
         reg [OPTION_OPERAND_WIDTH-1:0]           mul_opa;
         reg [OPTION_OPERAND_WIDTH-1:0]           mul_opb;
         reg [OPTION_OPERAND_WIDTH-1:0]           mul_result1;
         reg [OPTION_OPERAND_WIDTH-1:0]           mul_result2;
         reg [2:0]                                mul_valid_shr;

	 always @(posedge clk) begin
	    if (op_mul_i) begin
	       mul_opa <= a;
	       mul_opb <= b;
	    end
	    mul_result1 <= (mul_opa * mul_opb) & {OPTION_OPERAND_WIDTH{1'b1}};
	    mul_result2 <= mul_result1;
	 end

         assign mul_result = mul_result2;

         always @(posedge clk `OR_ASYNC_RST)
           if (rst)
             mul_valid_shr <= 3'b000;
           else if (decode_valid_i)
             mul_valid_shr <= {2'b00, op_mul_i};
           else
             mul_valid_shr <= mul_valid_shr[2] ? mul_valid_shr:
			      {mul_valid_shr[1:0], 1'b0};

         assign mul_valid = mul_valid_shr[2] & !decode_valid_i;

	 // Can't detect unsigned overflow in this implementation
	 assign mul_unsigned_overflow = 0;

      end // if (FEATURE_MULTIPLIER=="THREESTAGE")
      /* verilator lint_off WIDTH */
      else if (FEATURE_MULTIPLIER=="PIPELINED") begin : pipelinedmultiply
	 /* verilator lint_on WIDTH */
         // 32-bit multiplier in sync with cpu pipeline
         reg [OPTION_OPERAND_WIDTH-1:0]           mul_opa;
         reg [OPTION_OPERAND_WIDTH-1:0]           mul_opb;
         reg [OPTION_OPERAND_WIDTH-1:0]           mul_result1;

	 always @(posedge clk) begin
	    if (padv_execute_i) begin
	       mul_opa <= a;
	       mul_opb <= b;
	    end
	    if (padv_ctrl_i)
	      mul_result1 <= (mul_opa * mul_opb) & {OPTION_OPERAND_WIDTH{1'b1}};
	 end

         assign mul_result = mul_result1;

         assign mul_valid = 1;

	 // Can't detect unsigned overflow in this implementation
	 assign mul_unsigned_overflow = 0;

      end // if (FEATURE_MULTIPLIER=="PIPELINED")
      else if (FEATURE_MULTIPLIER=="SERIAL") begin : serialmultiply
         reg [(OPTION_OPERAND_WIDTH*2)-1:0]  mul_prod_r;
         reg [5:0]   serial_mul_cnt;
         reg         mul_done;
	 wire [OPTION_OPERAND_WIDTH-1:0] mul_a, mul_b;

	 // Check if it's a signed multiply and operand b is negative,
	 // convert to positive
	 assign mul_a = op_mul_signed_i & a[OPTION_OPERAND_WIDTH-1] ?
			~a + 1 : a;
	 assign mul_b = op_mul_signed_i & b[OPTION_OPERAND_WIDTH-1] ?
			~b + 1 : b;

         always @(posedge clk)
           if (rst) begin
               mul_prod_r <=  64'h0000_0000_0000_0000;
               serial_mul_cnt <= 6'd0;
               mul_done <= 1'b0;
            end
            else if (|serial_mul_cnt) begin
               serial_mul_cnt <= serial_mul_cnt - 6'd1;

               if (mul_prod_r[0])
                  mul_prod_r[(OPTION_OPERAND_WIDTH*2)-1:OPTION_OPERAND_WIDTH-1]
                     <= mul_prod_r[(OPTION_OPERAND_WIDTH*2)-1:OPTION_OPERAND_WIDTH] + mul_a;
               else
                  mul_prod_r[(OPTION_OPERAND_WIDTH*2)-1:OPTION_OPERAND_WIDTH-1]
                     <= {1'b0,mul_prod_r[(OPTION_OPERAND_WIDTH*2)-1:OPTION_OPERAND_WIDTH]};

               mul_prod_r[OPTION_OPERAND_WIDTH-2:0] <= mul_prod_r[OPTION_OPERAND_WIDTH-1:1];

               if (serial_mul_cnt==6'd1)
                  mul_done <= 1'b1;

            end
            else if (decode_valid_i && op_mul_i) begin
               mul_prod_r[(OPTION_OPERAND_WIDTH*2)-1:OPTION_OPERAND_WIDTH] <= 32'd0;
               mul_prod_r[OPTION_OPERAND_WIDTH-1:0] <= mul_b;
               mul_done <= 0;
               serial_mul_cnt <= 6'b10_0000;
            end
            else if (decode_valid_i) begin
               mul_done <= 1'b0;
            end

         assign mul_valid  = mul_done & !decode_valid_i;

         assign mul_result = op_mul_signed_i ?
			     ((a[OPTION_OPERAND_WIDTH-1] ^
			       b[OPTION_OPERAND_WIDTH-1]) ?
			      ~mul_prod_r[OPTION_OPERAND_WIDTH-1:0] + 1 :
			      mul_prod_r[OPTION_OPERAND_WIDTH-1:0]) :
			     mul_prod_r[OPTION_OPERAND_WIDTH-1:0];

	 assign mul_unsigned_overflow =  OPTION_OPERAND_WIDTH==64 ? 0 :
					 |mul_prod_r[(OPTION_OPERAND_WIDTH*2)-1:
						     OPTION_OPERAND_WIDTH];

	 // synthesis translate_off
	 `ifndef verilator
	 always @(posedge mul_valid)
	   begin
	      @(posedge clk);

	   if (((a*b) & {OPTION_OPERAND_WIDTH{1'b1}}) != mul_result)
	     begin
		$display("%t incorrect serial multiply result at pc %08h",
			 $time, pc_execute_i);
		$display("a=%08h b=%08h, mul_result=%08h, expected %08h",
			 a, b, mul_result, ((a*b) & {OPTION_OPERAND_WIDTH{1'b1}}));
	     end
	   end
	 `endif
         // synthesis translate_on

      end // if (FEATURE_MULTIPLIER=="SERIAL")
      else if (FEATURE_MULTIPLIER=="SIMULATION") begin
         // Simple multiplier result
	 wire [(OPTION_OPERAND_WIDTH*2)-1:0] mul_full_result;
	 assign mul_full_result = a * b;
         assign mul_result = mul_full_result[OPTION_OPERAND_WIDTH-1:0];

	 assign mul_unsigned_overflow =  OPTION_OPERAND_WIDTH==64 ? 0 :
	       |mul_full_result[(OPTION_OPERAND_WIDTH*2)-1:OPTION_OPERAND_WIDTH];

         assign mul_valid = 1;
      end
      else if (FEATURE_MULTIPLIER=="NONE") begin
         // No multiplier
         assign mul_result = adder_result;
         assign mul_valid = 1'b1;
	 assign mul_unsigned_overflow = 0;
      end
      else begin
         // Incorrect configuration option
         initial begin
            $display("%m: Error - chosen multiplier implementation (%s) not available",
                    FEATURE_MULTIPLIER);
            $finish;
         end
      end
   endgenerate

   // One signed overflow detection for all multiplication implmentations
   assign mul_signed_overflow = (FEATURE_MULTIPLIER=="NONE") ||
				(FEATURE_MULTIPLIER=="PIPELINED") ? 0 :
				// Same signs, check for negative result
				// (should be positive)
				((a[OPTION_OPERAND_WIDTH-1] ==
				  b[OPTION_OPERAND_WIDTH-1]) &&
				 mul_result[OPTION_OPERAND_WIDTH-1]) ||
				// Differring signs, check for positive result
				// (should be negative)
				((a[OPTION_OPERAND_WIDTH-1] ^
				  b[OPTION_OPERAND_WIDTH-1]) &&
				 !mul_result[OPTION_OPERAND_WIDTH-1]);

   assign mul_result_o = mul_result;

   generate
      /* verilator lint_off WIDTH */
      if (FEATURE_DIVIDER=="SERIAL") begin
      /* verilator lint_on WIDTH */
         reg [5:0] div_count;
         reg [OPTION_OPERAND_WIDTH-1:0] div_n;
         reg [OPTION_OPERAND_WIDTH-1:0] div_d;
         reg [OPTION_OPERAND_WIDTH-1:0] div_r;
         wire [OPTION_OPERAND_WIDTH:0]  div_sub;
         reg                            div_neg;
         reg                            div_done;
	 reg 				div_by_zero_r;


         assign div_sub = {div_r[OPTION_OPERAND_WIDTH-2:0],
                           div_n[OPTION_OPERAND_WIDTH-1]} - div_d;

         /* Cycle counter */
         always @(posedge clk `OR_ASYNC_RST)
           if (rst)
	     /* verilator lint_off WIDTH */
             div_count <= 0;
           else if (decode_valid_i)
             div_count <= OPTION_OPERAND_WIDTH;
	    /* verilator lint_on WIDTH */
           else if (|div_count)
             div_count <= div_count - 1;

         always @(posedge clk `OR_ASYNC_RST) begin
            if (rst) begin
               div_n <= 0;
               div_d <= 0;
               div_r <= 0;
               div_neg <= 1'b0;
               div_done <= 1'b0;
	       div_by_zero_r <= 1'b0;
            end else if (decode_valid_i & op_div_i) begin
	       div_n <= rfa_i;
               div_d <= rfb_i;
               div_r <= 0;
               div_neg <= 1'b0;
               div_done <= 1'b0;
	       div_by_zero_r <= !(|rfb_i);

               /*
                * Convert negative operands in the case of signed division.
                * If only one of the operands is negative, the result is
                * converted back to negative later on
                */
               if (op_div_signed_i) begin
                  if (rfa_i[OPTION_OPERAND_WIDTH-1] ^
		      rfb_i[OPTION_OPERAND_WIDTH-1])
                    div_neg <= 1'b1;

                  if (rfa_i[OPTION_OPERAND_WIDTH-1])
                    div_n <= ~rfa_i + 1;

                  if (rfb_i[OPTION_OPERAND_WIDTH-1])
                    div_d <= ~rfb_i + 1;
               end
            end else if (!div_done) begin
               if (!div_sub[OPTION_OPERAND_WIDTH]) begin // div_sub >= 0
                  div_r <= div_sub[OPTION_OPERAND_WIDTH-1:0];
                  div_n <= {div_n[OPTION_OPERAND_WIDTH-2:0], 1'b1};
               end else begin // div_sub < 0
                  div_r <= {div_r[OPTION_OPERAND_WIDTH-2:0],
                            div_n[OPTION_OPERAND_WIDTH-1]};
                  div_n <= {div_n[OPTION_OPERAND_WIDTH-2:0], 1'b0};
               end
               if (div_count == 1)
                 div_done <= 1'b1;
           end
         end

         assign div_valid = div_done & !decode_valid_i;
         assign div_result = div_neg ? ~div_n + 1 : div_n;
	 assign div_by_zero = div_by_zero_r;
      end
      /* verilator lint_off WIDTH */
      else if (FEATURE_DIVIDER=="SIMULATION") begin
      /* verilator lint_on WIDTH */
         assign div_result = a / b;
         assign div_valid = 1;
	 assign div_by_zero = (opc_alu_i == `OR1K_ALU_OPC_DIV ||
				 opc_alu_i == `OR1K_ALU_OPC_DIVU) && !(|b);

      end
      else if (FEATURE_DIVIDER=="NONE") begin
         assign div_result = adder_result;
         assign div_valid = 1'b1;
	 assign div_by_zero = 0;
      end
      else begin
         // Incorrect configuration option
         initial begin
            $display("%m: Error - chosen divider implementation (%s) not available",
                     FEATURE_DIVIDER);
            $finish;
         end
      end
   endgenerate


  // FPU related
  wire is_op_fpu;
  wire fpu_valid;
  wire [OPTION_OPERAND_WIDTH-1:0] fpu_result;
  reg  fpu_cmp_flag;
  wire fpu_op_is_comp;
  wire fpu_cmp_valid;
  generate
    /* verilator lint_off WIDTH */
    if (FEATURE_FPU=="ENABLED") begin : fpu_enabled_in_execute_alu
    /* verilator lint_on WIDTH */
      wire [`OR1K_FPUOP_WIDTH-1:0] opc_fpu; // alias for op_fpu_i with dropped MSB
      wire fpu_new_input;
      wire fpu_op_is_arith, fpu_op_is_conv;
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
      assign is_op_fpu = op_fpu_i[`OR1K_FPUOP_WIDTH-1];
      assign opc_fpu  = {1'b0,op_fpu_i[`OR1K_FPUOP_WIDTH-2:0]};

      assign fpu_new_input = decode_valid_i & is_op_fpu;
      
      assign fpu_op_is_arith = is_op_fpu & (!(|op_fpu_i[3:2]));
      assign fpu_op_is_conv  = is_op_fpu & (op_fpu_i[2] & !op_fpu_i[3]);   
      assign fpu_op_is_comp  = is_op_fpu & op_fpu_i[3];

      assign fpu_valid = !decode_valid_i &
                         ((fpu_op_is_arith & fpu_arith_done) |
                          (fpu_op_is_conv  & fpu_conv_done)  |
                          fpu_op_is_comp);
                          
      assign fpu_cmp_valid = !decode_valid_i; // for fpu flag set/clear logic

      assign fpcsr_set_o = fpu_valid;
   
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
      always @*
        begin
          // Get rid of top bit - is FPU op valid bit
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
      assign fpu_result = fpu_op_is_conv ? result_conv : result_arith;   
   
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
     end
     /* verilator lint_off WIDTH */
     else if (FEATURE_FPU=="NONE") begin : fpu_none_in_execute_alu
     /* verilator lint_on WIDTH */
       assign is_op_fpu  = 0;
       assign fpu_valid  = 1; // no block for alu
       assign fpu_result = {OPTION_OPERAND_WIDTH{1'b0}};
       assign fpcsr_o = {`OR1K_FPCSR_WIDTH{1'b0}};
       assign fpcsr_set_o = 0;
       assign fpu_op_is_comp = 0;
       assign fpu_cmp_valid = 0;
       always @(posedge clk) fpu_cmp_flag <= 0;
     end
     else begin : fpu_undef_in_execute_alu
         // Incorrect configuration option
       initial begin
         $display("%m: Error - chosen FPU implementation (%s) not available",
                     FEATURE_FPU);
         $finish;
       end
     end   
   endgenerate // FPU related


   wire ffl1_valid;
   generate
      if (FEATURE_FFL1!="NONE") begin
	 wire [OPTION_OPERAND_WIDTH-1:0] ffl1_result_wire;
	 assign ffl1_result_wire = (opc_alu_secondary_i[2]) ?
				   (a[31] ? 32 : a[30] ? 31 : a[29] ? 30 :
				    a[28] ? 29 : a[27] ? 28 : a[26] ? 27 :
				    a[25] ? 26 : a[24] ? 25 : a[23] ? 24 :
				    a[22] ? 23 : a[21] ? 22 : a[20] ? 21 :
				    a[19] ? 20 : a[18] ? 19 : a[17] ? 18 :
				    a[16] ? 17 : a[15] ? 16 : a[14] ? 15 :
				    a[13] ? 14 : a[12] ? 13 : a[11] ? 12 :
				    a[10] ? 11 : a[9] ? 10 : a[8] ? 9 :
				    a[7] ? 8 : a[6] ? 7 : a[5] ? 6 : a[4] ? 5 :
				    a[3] ? 4 : a[2] ? 3 : a[1] ? 2 : a[0] ? 1 : 0 ) :
				   (a[0] ? 1 : a[1] ? 2 : a[2] ? 3 : a[3] ? 4 :
				    a[4] ? 5 : a[5] ? 6 : a[6] ? 7 : a[7] ? 8 :
				    a[8] ? 9 : a[9] ? 10 : a[10] ? 11 : a[11] ? 12 :
				    a[12] ? 13 : a[13] ? 14 : a[14] ? 15 :
				    a[15] ? 16 : a[16] ? 17 : a[17] ? 18 :
				    a[18] ? 19 : a[19] ? 20 : a[20] ? 21 :
				    a[21] ? 22 : a[22] ? 23 : a[23] ? 24 :
				    a[24] ? 25 : a[25] ? 26 : a[26] ? 27 :
				    a[27] ? 28 : a[28] ? 29 : a[29] ? 30 :
				    a[30] ? 31 : a[31] ? 32 : 0);
	 /* verilator lint_off WIDTH */
	 if (FEATURE_FFL1=="REGISTERED") begin
	    /* verilator lint_on WIDTH */
	    reg [OPTION_OPERAND_WIDTH-1:0] ffl1_result_r;

	    assign ffl1_valid = !decode_valid_i;
	    assign ffl1_result = ffl1_result_r;

	    always @(posedge clk)
	      if (decode_valid_i)
		ffl1_result_r = ffl1_result_wire;
	 end else begin
	    assign ffl1_result = ffl1_result_wire;
	    assign ffl1_valid = 1'b1;
	 end
      end
      else begin
	 assign ffl1_result = adder_result;
	 assign ffl1_valid = 1'b1;
      end
   endgenerate

   // Xor result is zero if equal
   assign a_eq_b = !(|xor_result);
   // Signed compare
   assign a_lts_b = !(adder_result_sign == adder_signed_overflow);
   // Unsigned compare
   assign a_ltu_b = !adder_carryout;

   generate
      /* verilator lint_off WIDTH */
      if (OPTION_SHIFTER=="BARREL" &&
          FEATURE_SRA=="ENABLED" &&
          FEATURE_ROR=="ENABLED") begin : full_barrel_shifter
         /* verilator lint_on WIDTH */
         assign shift_valid = 1;
         assign shift_result =
                               (opc_alu_shr==`OR1K_ALU_OPC_SECONDARY_SHRT_SRA) ?
                               ({32{a[OPTION_OPERAND_WIDTH-1]}} <<
                                (/*7'd*/OPTION_OPERAND_WIDTH-{2'b0,b[4:0]})) |
                               a >> b[4:0] :
                               (opc_alu_shr==`OR1K_ALU_OPC_SECONDARY_SHRT_ROR) ?
                               (a << (6'd32-{1'b0,b[4:0]})) |
                               (a >> b[4:0]) :
                               (opc_alu_shr==`OR1K_ALU_OPC_SECONDARY_SHRT_SLL) ?
                               a << b[4:0] :
                               //(opc_alu_shr==`OR1K_ALU_OPC_SECONDARY_SHRT_SRL) ?
                               a >> b[4:0];
      end // if (OPTION_SHIFTER=="ENABLED" &&...
      /* verilator lint_off WIDTH */
      else if (OPTION_SHIFTER=="BARREL" &&
               FEATURE_SRA=="ENABLED" &&
               FEATURE_ROR!="ENABLED") begin : full_barrel_shifter_no_ror
	 /* verilator lint_on WIDTH */
         assign shift_valid = 1;
         assign shift_result =
                               (opc_alu_shr==`OR1K_ALU_OPC_SECONDARY_SHRT_SRA) ?
                               ({32{a[OPTION_OPERAND_WIDTH-1]}} <<
                                (/*7'd*/OPTION_OPERAND_WIDTH-{2'b0,b[4:0]})) |
                               a >> b[4:0] :
                               (opc_alu_shr==`OR1K_ALU_OPC_SECONDARY_SHRT_SLL) ?
                               a << b[4:0] :
                               //(opc_alu_shr==`OR1K_ALU_OPC_SECONDARY_SHRT_SRL) ?
                               a >> b[4:0];
      end // if (OPTION_SHIFTER=="ENABLED" &&...
      /* verilator lint_off WIDTH */
      else if (OPTION_SHIFTER=="BARREL" &&
               FEATURE_SRA!="ENABLED" &&
               FEATURE_ROR!="ENABLED") begin : full_barrel_shifter_no_ror_sra
	 /* verilator lint_on WIDTH */
         assign shift_valid = 1;
         assign shift_result =
                               (opc_alu_shr==`OR1K_ALU_OPC_SECONDARY_SHRT_SLL) ?
                               a << b[4:0] :
                               //(opc_alu_shr==`OR1K_ALU_OPC_SECONDARY_SHRT_SRL) ?
                               a >> b[4:0];
      end
      else if (OPTION_SHIFTER=="SERIAL") begin : serial_shifter
         // Serial shifter
         reg [4:0] shift_cnt;
         reg       shift_go;
         reg [OPTION_OPERAND_WIDTH-1:0] shift_result_r;
         always @(posedge clk `OR_ASYNC_RST)
           if (rst)
             shift_go <= 0;
           else if (decode_valid_i)
             shift_go <= op_shift_i;

         always @(posedge clk `OR_ASYNC_RST)
           if (rst) begin
              shift_cnt <= 0;
              shift_result_r <= 0;
           end
           else if (decode_valid_i & op_shift_i) begin
              shift_cnt <= 0;
              shift_result_r <= a;
           end
           else if (shift_go && !(shift_cnt==b[4:0])) begin
              shift_cnt <= shift_cnt + 1;
              if (opc_alu_shr==`OR1K_ALU_OPC_SECONDARY_SHRT_SRL)
                shift_result_r <= {1'b0,shift_result_r[OPTION_OPERAND_WIDTH-1:1]};
              else if (opc_alu_shr==`OR1K_ALU_OPC_SECONDARY_SHRT_SLL)
                shift_result_r <= {shift_result_r[OPTION_OPERAND_WIDTH-2:0],1'b0};
              else if (opc_alu_shr==`OR1K_ALU_OPC_SECONDARY_SHRT_ROR)
                shift_result_r <= {shift_result_r[0]
                                   ,shift_result_r[OPTION_OPERAND_WIDTH-1:1]};

              else if (opc_alu_shr==`OR1K_ALU_OPC_SECONDARY_SHRT_SRA)
                shift_result_r <= {a[OPTION_OPERAND_WIDTH-1],
                                   shift_result_r[OPTION_OPERAND_WIDTH-1:1]};
           end // if (shift_go && !(shift_cnt==b[4:0]))

         assign shift_valid = (shift_cnt==b[4:0]) & shift_go & !decode_valid_i;

         assign shift_result = shift_result_r;

      end // if (OPTION_SHIFTER=="SERIAL")
      else
         initial begin
            $display("%m: Error - chosen shifter implementation (%s) not available",
                     OPTION_SHIFTER);
            $finish;

      end
   endgenerate

   // Conditional move
   generate
      /* verilator lint_off WIDTH */
      if (FEATURE_CMOV=="ENABLED") begin
      /* verilator lint_on WIDTH */
         assign cmov_result = flag_i ? a : b;
      end
   endgenerate

   // Combinatorial block
   always @*
     case(opc_alu_secondary_i)
       `OR1K_COMP_OPC_EQ:
         flag_set = a_eq_b;
       `OR1K_COMP_OPC_NE:
         flag_set = !a_eq_b;
       `OR1K_COMP_OPC_GTU:
         flag_set = !(a_eq_b | a_ltu_b);
       `OR1K_COMP_OPC_GTS:
         flag_set = !(a_eq_b | a_lts_b);
       `OR1K_COMP_OPC_GEU:
         flag_set = !a_ltu_b;
       `OR1K_COMP_OPC_GES:
         flag_set = !a_lts_b;
       `OR1K_COMP_OPC_LTU:
         flag_set = a_ltu_b;
       `OR1K_COMP_OPC_LTS:
         flag_set = a_lts_b;
       `OR1K_COMP_OPC_LEU:
         flag_set = a_eq_b | a_ltu_b;
       `OR1K_COMP_OPC_LES:
         flag_set = a_eq_b | a_lts_b;
       default:
         flag_set = 0;
     endcase // case (opc_alu_secondary_i)


   // Comparison logic
   // To update SR[F] either from integer or float point comparision
   // FPU TODO: does forwading logic compatible with delay on fp-comparision???
   generate
     /* verilator lint_off WIDTH */
     if (FEATURE_FPU=="ENABLED") begin : fpu_enabled2_in_execute_alu
     /* verilator lint_on WIDTH */
       assign flag_set_o   = (fpu_op_is_comp ?
                              (fpu_cmp_flag & fpu_cmp_valid) :
                              (flag_set & op_setflag_i));
       assign flag_clear_o = (fpu_op_is_comp ?
                              (!fpu_cmp_flag & fpu_cmp_valid) :
                              (!flag_set & op_setflag_i));
     end
     else begin : fpu_undef2_in_execute_alu
       assign flag_set_o = flag_set & op_setflag_i;
       assign flag_clear_o = !flag_set & op_setflag_i;
     end
   endgenerate


   // Logic operations
   assign and_result = a & b;
   assign or_result = a | b;
   assign xor_result = a ^ b;

   assign op_and = op_alu_i & opc_alu_i == `OR1K_ALU_OPC_AND;
   assign op_or = op_alu_i & opc_alu_i == `OR1K_ALU_OPC_OR;
   assign op_xor = op_alu_i & opc_alu_i == `OR1K_ALU_OPC_XOR;
   assign op_cmov = op_alu_i & opc_alu_i == `OR1K_ALU_OPC_CMOV;

   // Result muxing - result is registered in RF
   assign alu_result_o = op_and ? and_result :
			 op_or | op_mfspr_i | op_mtspr_i ? or_result :
			 op_xor ? xor_result :
			 op_cmov ? cmov_result :
			 op_movhi_i ? immediate_i :
          is_op_fpu ? fpu_result :
			 op_mul_i ? mul_result[OPTION_OPERAND_WIDTH-1:0] :
			 op_shift_i ? shift_result :
			 op_div_i ? div_result :
			 op_ffl1_i ? ffl1_result :
			 adder_result;

   // Carry and overflow flag generation
   assign overflow_set_o = op_add_i & adder_signed_overflow |
			   op_mul_signed_i & mul_signed_overflow |
			   op_div_signed_i & div_by_zero;

   assign overflow_clear_o = op_add_i & !adder_signed_overflow |
			     op_mul_signed_i & !mul_signed_overflow |
			     op_div_signed_i & !div_by_zero;

   assign carry_set_o = op_add_i & adder_unsigned_overflow |
			op_mul_unsigned_i & mul_unsigned_overflow |
			op_div_unsigned_i & div_by_zero;

   assign carry_clear_o = op_add_i & !adder_unsigned_overflow |
			  op_mul_unsigned_i & !mul_unsigned_overflow |
			  op_div_unsigned_i & !div_by_zero;

   // Stall logic for multicycle ALU operations
   assign alu_stall = op_div_i & !div_valid |
		      op_mul_i & !mul_valid |
            is_op_fpu & !fpu_valid |
		      op_shift_i & !shift_valid |
		      op_ffl1_i & !ffl1_valid;

   assign alu_valid_o = !alu_stall;

endmodule // mor1kx_execute_alu
