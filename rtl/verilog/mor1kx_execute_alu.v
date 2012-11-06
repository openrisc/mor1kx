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
  (/*AUTOARG*/
   // Outputs
   flag_set_o, flag_clear_o, alu_result_o, alu_valid_o,
   // Inputs
   clk, rst, padv_i, opc_alu_i, opc_alu_secondary_i, imm16_i,
   opc_insn_i, decode_valid_i, op_jbr_i, op_jr_i, immjbr_upper_i,
   pc_execute_i, rfa_i, rfb_i, flag_i
   );


   parameter OPTION_OPERAND_WIDTH = 32;

   parameter FEATURE_MULTIPLIER = "THREESTAGE";
   parameter FEATURE_DIVIDER = "NONE";

   parameter FEATURE_ADDC = "NONE";
   parameter FEATURE_SRA = "ENABLED";
   parameter FEATURE_ROR = "NONE";
   parameter FEATURE_EXT = "NONE";
   parameter FEATURE_CMOV = "NONE";
   parameter FEATURE_FFL1 = "NONE";

   parameter FEATURE_CUST1 = "NONE";
   parameter FEATURE_CUST2 = "NONE";
   parameter FEATURE_CUST3 = "NONE";
   parameter FEATURE_CUST4 = "NONE";
   parameter FEATURE_CUST5 = "NONE";
   parameter FEATURE_CUST6 = "NONE";
   parameter FEATURE_CUST7 = "NONE";
   parameter FEATURE_CUST8 = "NONE";

   parameter OPTION_SHIFTER = "BARREL";

   input clk, rst;

   // pipeline control signal in
   input padv_i;

   // inputs to ALU
   input [`OR1K_ALU_OPC_WIDTH-1:0] opc_alu_i;
   input [`OR1K_ALU_OPC_WIDTH-1:0] opc_alu_secondary_i;

   input [`OR1K_IMM_WIDTH-1:0]    imm16_i;

   input [`OR1K_OPCODE_WIDTH-1:0] opc_insn_i;

   input                          decode_valid_i;


   input                          op_jbr_i, op_jr_i;
   input [9:0]                    immjbr_upper_i;
   input [OPTION_OPERAND_WIDTH-1:0] pc_execute_i;

   input [OPTION_OPERAND_WIDTH-1:0] rfa_i;
   input [OPTION_OPERAND_WIDTH-1:0] rfb_i;

   // flag fed back from ctrl
   input                            flag_i;

   output                            flag_set_o,
                                     flag_clear_o;

   output [OPTION_OPERAND_WIDTH-1:0] alu_result_o;
   output                            alu_valid_o;

   reg                                   alu_valid; /* combinatorial */


   wire                                   comp_op;

   wire [OPTION_OPERAND_WIDTH-1:0]        a;
   wire [OPTION_OPERAND_WIDTH-1:0]        b;

   // Adder & comparator wires
   wire [OPTION_OPERAND_WIDTH-1:0]        adder_result;
   wire                                   adder_carryout;

   wire [OPTION_OPERAND_WIDTH-1:0]        b_neg;
   wire [OPTION_OPERAND_WIDTH-1:0]        b_mux;
   wire                                   carry_in;

   wire                                   a_eq_b;
   wire                                   a_lt_b;
   wire                                   adder_do_sub;

   // Shifter wires
   wire [`OR1K_ALU_OPC_SECONDARY_WIDTH-1:0] opc_alu_shr;
   wire                                   shift_op;
   wire [OPTION_OPERAND_WIDTH-1:0]        shift_result;
   wire                                   shift_valid;

   wire                                   alu_result_valid;
   reg [OPTION_OPERAND_WIDTH-1:0]         alu_result;  // comb.


   // Comparison wires
   reg                                    flag_set; // comb.

   // Logic wires
   wire [OPTION_OPERAND_WIDTH-1:0]        and_result;
   wire [OPTION_OPERAND_WIDTH-1:0]        or_result;
   wire [OPTION_OPERAND_WIDTH-1:0]        xor_result;

   // Multiplier wires
   wire                                   mul_op;
   wire                                   mul_op_signed;
   wire [OPTION_OPERAND_WIDTH-1:0]        mul_result;
   wire                                   mul_valid;

   wire [OPTION_OPERAND_WIDTH-1:0]        div_result;
   wire                                   div_valid;

   wire [OPTION_OPERAND_WIDTH-1:0]        ffl1_result;

   wire [OPTION_OPERAND_WIDTH-1:0]        cmov_result;


   // First stage signals - detect which operands we should take
   wire                                   operandb_sext_imm;
   wire                                   operandb_zext_imm;

   assign operandb_sext_imm = ((opc_insn_i[5:4] == 2'b10) &
                             ~(opc_insn_i==`OR1K_OPCODE_ORI) &
                             ~(opc_insn_i==`OR1K_OPCODE_ANDI)) |
                             (opc_insn_i==`OR1K_OPCODE_SW) |
                             (opc_insn_i==`OR1K_OPCODE_SH) |
                             (opc_insn_i==`OR1K_OPCODE_SB);

   assign operandb_zext_imm = ((opc_insn_i[5:4] == 2'b10) &
                              ((opc_insn_i==`OR1K_OPCODE_ORI) |
                               (opc_insn_i==`OR1K_OPCODE_ANDI))) |
                             (opc_insn_i==`OR1K_OPCODE_MTSPR);

   assign a = (op_jbr_i | op_jr_i) ? pc_execute_i : rfa_i;
   assign b = operandb_sext_imm ? {{16{imm16_i[15]}},imm16_i[15:0]} :
              operandb_zext_imm ? {{16{1'b0}},imm16_i[15:0]} :
              (opc_insn_i==`OR1K_OPCODE_MOVHI) ? {imm16_i,16'd0} :
              op_jbr_i ? {{4{immjbr_upper_i[9]}},immjbr_upper_i,imm16_i,2'b00} :
              rfb_i ;

   assign comp_op = opc_insn_i==`OR1K_OPCODE_SF ||
                    opc_insn_i==`OR1K_OPCODE_SFIMM;

   assign opc_alu_shr = opc_alu_secondary_i[`OR1K_ALU_OPC_SECONDARY_WIDTH-1:0];

   // Subtract when comparing to check if equal
   assign adder_do_sub = (opc_insn_i==`OR1K_OPCODE_ALU &
                          opc_alu_i==`OR1K_ALU_OPC_SUB) |
                         comp_op;

   // Adder/subtractor inputs
   assign b_neg = ~b;
   assign carry_in = adder_do_sub;
   assign b_mux = adder_do_sub ? b_neg : b;
   // Adder
   assign {adder_carryout, adder_result} = a + b_mux +
                                           {{OPTION_OPERAND_WIDTH-1{1'b0}},
                                            carry_in};

   assign mul_op = (opc_insn_i==`OR1K_OPCODE_ALU &&
                    (opc_alu_i == `OR1K_ALU_OPC_MUL ||
                     opc_alu_i == `OR1K_ALU_OPC_MULU)) ||
                   opc_insn_i == `OR1K_OPCODE_MULI;

   assign mul_op_signed = (opc_insn_i==`OR1K_OPCODE_ALU &&
                           opc_alu_i == `OR1K_ALU_OPC_MUL) ||
                          opc_insn_i == `OR1K_OPCODE_MULI;

   generate
      /* verilator lint_off WIDTH */
      if (FEATURE_MULTIPLIER=="THREESTAGE") begin : threestagemultiply
	 /* verilator lint_on WIDTH */
         // 32-bit multiplier with three registering stages to help with timing
         reg [OPTION_OPERAND_WIDTH-1:0]           mul_opa, mul_opb, mul_result1, mul_result2;
         reg [2:0]                                mul_valid_shr;

         always @(posedge clk)
	   if (rst)
	     mul_result1 <= {OPTION_OPERAND_WIDTH{1'b0}};
	   else
           begin
              if (decode_valid_i && mul_op)
                begin
                   mul_opa       <= a;
                   mul_opb       <= b;
                end

              if (mul_valid_shr==3'b001)
                mul_result1   <= (mul_opa * mul_opb) & {OPTION_OPERAND_WIDTH{1'b1}};
              mul_result2 <= mul_result1;
           end

         assign mul_result = mul_result2;

         always @(posedge clk `OR_ASYNC_RST)
           if (rst)
             mul_valid_shr <= 3'b000;
           else if (decode_valid_i)
             mul_valid_shr <= {2'b00, mul_op};
           else
             mul_valid_shr <= mul_valid_shr[2] ? mul_valid_shr:
			      {mul_valid_shr[1:0], 1'b0};

         assign mul_valid = mul_valid_shr[2] & !decode_valid_i;

      end // if (FEATURE_MULTIPLIER=="THREESTAGE")
      else if (FEATURE_MULTIPLIER=="SERIAL") begin : serialmultiply
         reg [(OPTION_OPERAND_WIDTH*2)-1:0]  mul_prod_r;
         reg [5:0]   serial_mul_cnt;
         reg         mul_done;
	 wire [OPTION_OPERAND_WIDTH-1:0] mul_a, mul_b;

	 // Check if it's a signed multiply and operand b is negative, convert to positive
	 assign mul_a = mul_op_signed & a[OPTION_OPERAND_WIDTH-1] ?
					  ~a + 1 : a;
	 assign mul_b = mul_op_signed & b[OPTION_OPERAND_WIDTH-1] ?
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
            else if (decode_valid_i && mul_op/* && !mul_done*/) begin
               mul_prod_r[(OPTION_OPERAND_WIDTH*2)-1:OPTION_OPERAND_WIDTH] <= 32'd0;
               mul_prod_r[OPTION_OPERAND_WIDTH-1:0] <= mul_b;
               mul_done <= 0;
               serial_mul_cnt <= 6'b10_0000;
            end
            else if (decode_valid_i) begin
               mul_done <= 1'b0;
            end

         assign mul_valid  = mul_done & !decode_valid_i;

         assign mul_result = mul_op_signed ? ((a[OPTION_OPERAND_WIDTH-1] ^
                                               b[OPTION_OPERAND_WIDTH-1]) ?
                             ~mul_prod_r[OPTION_OPERAND_WIDTH-1:0] + 1 :
                             mul_prod_r[OPTION_OPERAND_WIDTH-1:0]) :
                             mul_prod_r[OPTION_OPERAND_WIDTH-1:0];


	 // synthesis translate_off
	 `ifndef verilator
	 always @(posedge mul_valid)
	   begin
	      @(posedge clk);

	   if (((a*b) & {OPTION_OPERAND_WIDTH{1'b1}}) != mul_result)
	     begin
		$display("%t incorrect serial multiply result at pc %08h", $time, pc_execute_i);
		$display("a=%08h b=%08h, mul_result=%08h, expected %08h",a, b, mul_result, ((a*b) & {OPTION_OPERAND_WIDTH{1'b1}}));
	     end
	   end
	 `endif
         // synthesis translate_on

      end // if (FEATURE_MULTIPLIER=="SERIAL")
      else if (FEATURE_MULTIPLIER=="SIMULATION") begin
         // Simple multiplier result
         assign mul_result = a * b;
         assign mul_valid = 1;
      end
      else if (FEATURE_MULTIPLIER=="NONE") begin
         // No multiplier
         assign mul_result = adder_result;
         assign mul_valid = alu_result_valid;
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

   generate
      if (FEATURE_DIVIDER=="SERIAL") begin
         reg [4:0] div_count;
         reg [OPTION_OPERAND_WIDTH-1:0] div_n;
         reg [OPTION_OPERAND_WIDTH-1:0] div_d;
         reg [OPTION_OPERAND_WIDTH-1:0] div_r;
         wire [OPTION_OPERAND_WIDTH:0]  div_sub;
         reg                            div_neg;
         reg                            div_done;

         assign div_sub = {div_r[OPTION_OPERAND_WIDTH-2:0],
                           div_n[OPTION_OPERAND_WIDTH-1]} - div_d;

         /* Cycle counter */
         always @(posedge clk `OR_ASYNC_RST)
           if (rst)
	     /* verilator lint_off WIDTH */
             div_count <= OPTION_OPERAND_WIDTH-1;
           else if (decode_valid_i)
             div_count <= OPTION_OPERAND_WIDTH-1;
	    /* verilator lint_on WIDTH */
           else
             div_count <= div_count - 1;

         always @(posedge clk `OR_ASYNC_RST) begin
            if (rst) begin
               div_n <= a;
               div_d <= b;
               div_r <= 0;
               div_neg <= 1'b0;
               div_done <= 1'b0;
            end else if (decode_valid_i) begin
               div_n <= a;
               div_d <= b;
               div_r <= 0;
               div_neg <= 1'b0;
               div_done <= 1'b0;
               /*
                * Convert negative operands in the case of signed division.
                * If only one of the operands is negative, the result is
                * converted back to negative later on
                */
               if (opc_alu_i == `OR1K_ALU_OPC_DIV) begin
                  if (a[OPTION_OPERAND_WIDTH-1] ^ b[OPTION_OPERAND_WIDTH-1])
                    div_neg <= 1'b1;

                  if (a[OPTION_OPERAND_WIDTH-1])
                    div_n <= ~a + 1;

                  if (b[OPTION_OPERAND_WIDTH-1])
                    div_d <= ~b + 1;
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
               if (div_count == 0)
                 div_done <= 1'b1;
           end
         end

         assign div_valid = div_done & !decode_valid_i;
         assign div_result = div_neg ? ~div_n + 1 : div_n;
      end
      else if (FEATURE_DIVIDER=="SIMULATION") begin
         assign div_result = a / b;
         assign div_valid = 1;
      end
      else if (FEATURE_DIVIDER=="NONE") begin
         assign div_result = adder_result;
         assign div_valid = alu_result_valid;
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

	 if (FEATURE_FFL1=="REGISTERED") begin
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
	 assign ffl1_valid = alu_result_valid;
      end
   endgenerate

   // Adder result is zero if equal
   assign a_eq_b = !(|adder_result);
   assign a_lt_b = opc_alu_secondary_i[3] ? // Signed compare
                   ((a[OPTION_OPERAND_WIDTH-1] &
                     !b[OPTION_OPERAND_WIDTH-1]) |
                    (!a[OPTION_OPERAND_WIDTH-1] &
                     !b[OPTION_OPERAND_WIDTH-1] &
                     adder_result[OPTION_OPERAND_WIDTH-1]) |
                    (a[OPTION_OPERAND_WIDTH-1] &
                     b[OPTION_OPERAND_WIDTH-1] &
                     adder_result[OPTION_OPERAND_WIDTH-1])) :
                   (a < b);
   /*
                   // Unsigned compare
                   // check for a < b: if result of a - b has wrapped
                   adder_result[OPTION_OPERAND_WIDTH-1] &&
                   // and check that a >>> b
                   !(a[OPTION_OPERAND_WIDTH-1] & !b[OPTION_OPERAND_WIDTH-1]);
   */

   assign shift_op = (opc_alu_i == `OR1K_ALU_OPC_SHRT ||
                      opc_insn_i == `OR1K_OPCODE_SHRTI) ;

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
               FEATURE_ROR!="ENABLED") begin : bull_barrel_shifter_no_ror
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
               FEATURE_ROR!="ENABLED") begin : bull_barrel_shifter_no_ror_sra
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
             shift_go <= shift_op;

         always @(posedge clk `OR_ASYNC_RST)
           if (rst) begin
              shift_cnt <= 0;
              shift_result_r <= 0;
           end
           else if (decode_valid_i & shift_op) begin
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
      if (FEATURE_CMOV=="ENABLED") begin
         assign cmov_result = flag_i ? a : b;
      end
   endgenerate

   // Comparison logic
   assign flag_set_o = flag_set & comp_op;
   assign flag_clear_o = !flag_set & comp_op;

   // Combinatorial block
   always @*
     case(opc_alu_secondary_i)
       `OR1K_COMP_OPC_EQ:
         flag_set = a_eq_b;
       `OR1K_COMP_OPC_NE:
         flag_set = !a_eq_b;
       `OR1K_COMP_OPC_GTU,
         `OR1K_COMP_OPC_GTS:
           flag_set = !(a_eq_b | a_lt_b);
       `OR1K_COMP_OPC_GEU,
         `OR1K_COMP_OPC_GES:
           flag_set = !a_lt_b;
       `OR1K_COMP_OPC_LTU,
         `OR1K_COMP_OPC_LTS:
           flag_set = a_lt_b;
       `OR1K_COMP_OPC_LEU,
         `OR1K_COMP_OPC_LES:
           flag_set = a_eq_b | a_lt_b;
       default:
         flag_set = 0;
     endcase // case (opc_alu_secondary_i)


   // Logic operations
   assign and_result = a & b;
   assign or_result = a | b;
   assign xor_result = a ^ b;


   // Result muxing - result is registered in RF
   always @*
     case(opc_insn_i)
       `OR1K_OPCODE_ALU:
         case(opc_alu_i)
/*
           `OR1K_ALU_OPC_ADDC,
           `OR1K_ALU_OPC_ADD:
             alu_result = adder_result;
           `OR1K_ALU_OPC_SUB:
             alu_result = adder_result;
*/
           `OR1K_ALU_OPC_AND:
             alu_result = and_result;
           `OR1K_ALU_OPC_OR:
             alu_result = or_result;
           `OR1K_ALU_OPC_XOR:
             alu_result = xor_result;
           `OR1K_ALU_OPC_MUL,
           `OR1K_ALU_OPC_MULU:
             alu_result = mul_result[OPTION_OPERAND_WIDTH-1:0];
           `OR1K_ALU_OPC_SHRT:
             alu_result = shift_result;
           `OR1K_ALU_OPC_DIV,
           `OR1K_ALU_OPC_DIVU:
             alu_result = div_result;
           `OR1K_ALU_OPC_FFL1:
             alu_result = ffl1_result;
           `OR1K_ALU_OPC_CMOV:
             alu_result = cmov_result;
             default:
               alu_result = adder_result;
           endcase // case (opc_alu_i)
         `OR1K_OPCODE_SHRTI:
           alu_result = shift_result;
         `OR1K_OPCODE_ADDIC,
         `OR1K_OPCODE_ADDI:
           alu_result = adder_result;
         `OR1K_OPCODE_ANDI:
           alu_result = and_result;
         `OR1K_OPCODE_ORI:
           alu_result = or_result;
         `OR1K_OPCODE_XORI:
           alu_result = xor_result;
         `OR1K_OPCODE_MULI:
           alu_result = mul_result[OPTION_OPERAND_WIDTH-1:0];
         `OR1K_OPCODE_SW,
         `OR1K_OPCODE_SH,
         `OR1K_OPCODE_SB,
         `OR1K_OPCODE_LWZ,
         `OR1K_OPCODE_LWS,
         `OR1K_OPCODE_LBZ,
         `OR1K_OPCODE_LBS,
         `OR1K_OPCODE_LHZ,
         `OR1K_OPCODE_LHS:
           alu_result = adder_result;
         `OR1K_OPCODE_MOVHI:
           alu_result = b;
         `OR1K_OPCODE_MFSPR,
         `OR1K_OPCODE_MTSPR:
           alu_result = or_result;
         `OR1K_OPCODE_J,
         `OR1K_OPCODE_JAL,
         `OR1K_OPCODE_BNF,
         `OR1K_OPCODE_BF,
         `OR1K_OPCODE_JR,
         `OR1K_OPCODE_JALR:
           alu_result = adder_result;
       default:
         // Default out is b - for jump reg instructions
         alu_result = b;
       endcase // case (opc_insn_i)

   assign alu_result_valid = 1'b1; // ALU (adder, logic ops) always ready
   assign alu_result_o = alu_result;

   // ALU finished/valid MUXing
   always @*
     case(opc_insn_i)
       `OR1K_OPCODE_ALU:
         case(opc_alu_i)
           `OR1K_ALU_OPC_MUL,
             `OR1K_ALU_OPC_MULU:
               alu_valid = mul_valid;

           `OR1K_ALU_OPC_DIV,
             `OR1K_ALU_OPC_DIVU:
               alu_valid = div_valid;

           `OR1K_ALU_OPC_FFL1:
             alu_valid = ffl1_valid;

           `OR1K_ALU_OPC_SHRT:
             alu_valid = shift_valid;

           default:
             alu_valid = alu_result_valid;
         endcase // case (opc_alu_i)

       `OR1K_OPCODE_MULI:
         alu_valid = mul_valid;

       `OR1K_OPCODE_SHRTI:
         alu_valid = shift_valid;
       default:
         alu_valid = alu_result_valid;
     endcase // case (opc_insn_i)


   assign alu_valid_o = alu_valid;

endmodule // mor1kx_execute_alu
