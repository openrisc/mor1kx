/* ****************************************************************************
  This Source Code Form is subject to the terms of the 
  Open Hardware Description License, v. 1.0. If a copy 
  of the OHDL was not distributed with this file, You 
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: mor1kx decode unit
  
  Outputs:
   - ALU operation
   - indication of other type of op - LSU/SPR
   - immediates
   - register file addresses
   - exception decodes:  illegal, system call
   
  Copyright (C) 2012 Authors
 
  Author(s): Julius Baxter <juliusbaxter@gmail.com>
 
***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_decode
  (
   clk, rst,

   // pipeline control signal in
   padv_i,

   // input from fetch stage
   pc_decode_i, decode_insn_i,

   // input from control stage
   pipeline_flush_i,

   // outputs to ALU
   opc_alu_o, opc_alu_secondary_o, imm16_o, immjbr_upper_o,

   // GPR numbers
   rfd_adr_o, rfa_adr_o, rfb_adr_o,

   // register file writeback enable
   rf_wb_o,

   // jump or branch op against immediate
   op_jbr_o,
   op_jr_o,
   op_jal_o,
  
   // indicate if we're an ALU operation
   op_alu_o,
  
   // inidicate if is LSU load or store
   op_lsu_load_o, op_lsu_store_o,

   // indicate it's a mfspr operation
   op_mfspr_o,

   // exceptions in
   decode_except_ibus_err_i,

   // exception output -
   execute_except_ibus_err_o, 
   execute_except_illegal_o, execute_except_syscall_o, execute_except_trap_o,

   // output is valid, signal
   pc_execute_o, decode_valid_o,

   // insn opcode, indicating what's going on
   opc_insn_o
   );

   parameter OPTION_OPERAND_WIDTH = 32;
   parameter OPTION_RESET_PC = {{(OPTION_OPERAND_WIDTH-13){1'b0}},
				`OR1K_RESET_VECTOR,8'd0};
   parameter OPTION_RF_ADDR_WIDTH = 5;
   
   parameter FEATURE_SYSCALL = "ENABLED";
   parameter FEATURE_TRAP = "ENABLED";
   parameter FEATURE_RANGE = "ENABLED";
   parameter FEATURE_MAC = "NONE";
   parameter FEATURE_MULTIPLIER = "PARALLEL";
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

   parameter REGISTERED_DECODE = "ENABLED";
   
   input clk, rst;

   // pipeline control signal in
   input padv_i;
   
   // input from fetch stage
   input [OPTION_OPERAND_WIDTH-1:0] pc_decode_i;
   input [`OR1K_INSN_WIDTH-1:0]     decode_insn_i;

   input 			    pipeline_flush_i;

   //outputs to ALU
   output reg [`OR1K_ALU_OPC_WIDTH-1:0] opc_alu_o;
   wire [`OR1K_ALU_OPC_WIDTH-1:0] 	opc_alu;
   output reg [`OR1K_ALU_OPC_WIDTH-1:0] opc_alu_secondary_o;
   wire [`OR1K_ALU_OPC_WIDTH-1:0] 	opc_alu_secondary;
   
   output reg [`OR1K_IMM_WIDTH-1:0] 	imm16_o;
   wire [`OR1K_IMM_WIDTH-1:0] 		imm16;
   
   // Upper 10 bits of immediate for jumps and branches
   output reg [9:0] 			immjbr_upper_o;
   wire [9:0] 				immjbr_upper;

   // GPR numbers
   output [OPTION_RF_ADDR_WIDTH-1:0] 	rfd_adr_o;
   output [OPTION_RF_ADDR_WIDTH-1:0] 	rfa_adr_o;
   output [OPTION_RF_ADDR_WIDTH-1:0] 	rfb_adr_o;

   output reg 				rf_wb_o;

   output reg 				op_jbr_o;
   output reg 				op_jr_o;
   output reg 				op_jal_o;

   output reg 				op_alu_o;
   
   output reg 				op_lsu_load_o, op_lsu_store_o;

   output reg 				op_mfspr_o;

   // exceptions in
   input 				decode_except_ibus_err_i;
   
   // exception output -
   output reg 				execute_except_ibus_err_o,
					execute_except_illegal_o, 
					execute_except_syscall_o,
					execute_except_trap_o;
   reg 					execute_except_illegal;
   
   wire 				execute_except_ibus_err,
					execute_except_syscall,
					execute_except_trap;
   
   // output is valid, signal
   output reg [OPTION_OPERAND_WIDTH-1:0] pc_execute_o;
   wire [OPTION_OPERAND_WIDTH-1:0] 	 pc_execute;
   
   output reg 				 decode_valid_o;
   
   
   output reg [`OR1K_OPCODE_WIDTH-1:0] 	 opc_insn_o;
   wire [`OR1K_OPCODE_WIDTH-1:0] 	 opc_insn;
   

   wire 				 rf_wb;
   
   wire 				 op_load;   
   wire 				 op_store;
   wire 				 opc_mtspr;
   wire 				 opc_setflag;
   wire 				 op_alu;
   wire 				 op_jbr;
   wire 				 op_jr;
   wire 				 op_jal;
   wire 				 op_mfspr;

   // load opcodes are 6'b10_0000 to 6'b10_0110, 0 to 6, so check for 7 and up
   assign op_load = (decode_insn_i[31:30]==2'b10) & !(&decode_insn_i[28:26])& 
		    !decode_insn_i[29];
   
   // Detect when instruction is store
   assign op_store = (decode_insn_i[`OR1K_OPCODE_SELECT] == `OR1K_OPCODE_SW) ||
		     (decode_insn_i[`OR1K_OPCODE_SELECT] == `OR1K_OPCODE_SB) ||
		     (decode_insn_i[`OR1K_OPCODE_SELECT] == `OR1K_OPCODE_SH);

   assign opc_mtspr = (decode_insn_i[`OR1K_OPCODE_SELECT] == 
		       `OR1K_OPCODE_MTSPR);

   // Detect when setflag instruction
   assign opc_setflag = decode_insn_i[`OR1K_OPCODE_SELECT] == `OR1K_OPCODE_SF ||
			decode_insn_i[`OR1K_OPCODE_SELECT] == 
			`OR1K_OPCODE_SFIMM;
   
   // Detect which instructions will be generating a result from the ALU
   assign op_alu = ((decode_insn_i[31:30]==2'b10) &
		    //l.addi and the rest...
		    (decode_insn_i[28:26]==3'b111 | decode_insn_i[29])) |
		   // all normal ALU ops, and l.cust5-8
		   decode_insn_i[31:29]==3'b111 |
		   // l.mt/fspr - need address out of ALU
		   opc_mtspr |
		   (decode_insn_i[`OR1K_OPCODE_SELECT] == `OR1K_OPCODE_MFSPR) |
		   (decode_insn_i[`OR1K_OPCODE_SELECT]==`OR1K_OPCODE_MOVHI);

   // Bottom 4 opcodes branch against an immediate
   assign op_jbr = decode_insn_i[`OR1K_OPCODE_SELECT] < `OR1K_OPCODE_NOP;

   assign op_jr = decode_insn_i[`OR1K_OPCODE_SELECT]==`OR1K_OPCODE_JR |
		  decode_insn_i[`OR1K_OPCODE_SELECT]==`OR1K_OPCODE_JALR;

   assign op_jal = decode_insn_i[`OR1K_OPCODE_SELECT]==`OR1K_OPCODE_JALR |
		   decode_insn_i[`OR1K_OPCODE_SELECT]==`OR1K_OPCODE_JAL;

   assign op_mfspr = decode_insn_i[`OR1K_OPCODE_SELECT]==`OR1K_OPCODE_MFSPR;
   
   // Which instructions cause writeback?
   assign rf_wb = (decode_insn_i[`OR1K_OPCODE_SELECT]==`OR1K_OPCODE_JAL |
		   decode_insn_i[`OR1K_OPCODE_SELECT]==`OR1K_OPCODE_MOVHI |
		   decode_insn_i[`OR1K_OPCODE_SELECT]==`OR1K_OPCODE_JALR) |
		  // All '10????' opcodes except l.sfxxi
		  (decode_insn_i[31:30]==2'b10 & 
		   !(decode_insn_i[`OR1K_OPCODE_SELECT]==`OR1K_OPCODE_SFIMM)) |
		  // All '11????' opcodes except l.sfxx and l.mtspr
		  (decode_insn_i[31:30]==2'b11 & 
		   !(decode_insn_i[`OR1K_OPCODE_SELECT]==`OR1K_OPCODE_SF | 
		     opc_mtspr | op_store));


   // Register file addresses are not registered here, but rather go
   // straight out to RF so read is done when execute stage is ready
   assign rfd_adr_o = op_jal ? 9 : 
		      decode_insn_i[`OR1K_RD_SELECT];
   assign rfa_adr_o = decode_insn_i[`OR1K_RA_SELECT];
   assign rfb_adr_o = decode_insn_i[`OR1K_RB_SELECT];
   
   // Insn opcode
   assign opc_insn = decode_insn_i[`OR1K_OPCODE_SELECT];   
   // Immediate in l.mtspr is broken up, reassemble
   assign imm16 = (opc_mtspr | op_store) ? 
		  {decode_insn_i[25:21],decode_insn_i[10:0]} : 
		  decode_insn_i[`OR1K_IMM_SELECT];
   
   
   // Upper 10 bits for jump/branch instructions
   assign immjbr_upper = decode_insn_i[25:16];
   
   
   // ALU opcode
   assign opc_alu = (op_jbr | op_jal) ? `OR1K_ALU_OPC_ADD : 
		    decode_insn_i[`OR1K_ALU_OPC_SELECT];
   assign opc_alu_secondary = opc_setflag ? 
			      decode_insn_i[`OR1K_COMP_OPC_SELECT]:
			      {1'b0,
			       decode_insn_i[`OR1K_ALU_OPC_SECONDAY_SELECT]};

   assign execute_except_ibus_err = decode_except_ibus_err_i;

   assign execute_except_syscall = decode_insn_i[`OR1K_OPCODE_SELECT] == 
				   `OR1K_OPCODE_SYSTRAPSYNC &&
				   decode_insn_i[`OR1K_SYSTRAPSYNC_OPC_SELECT] ==
				   `OR1K_SYSTRAPSYNC_OPC_SYSCALL;
   assign execute_except_trap = decode_insn_i[`OR1K_OPCODE_SELECT] == 
				`OR1K_OPCODE_SYSTRAPSYNC &&
				decode_insn_i[`OR1K_SYSTRAPSYNC_OPC_SELECT] ==
				`OR1K_SYSTRAPSYNC_OPC_TRAP;
   
   assign pc_execute = pc_decode_i;

   // Illegal instruction decode
   always @*
     case (decode_insn_i[`OR1K_OPCODE_SELECT])
       `OR1K_OPCODE_J,
       `OR1K_OPCODE_JAL,
       `OR1K_OPCODE_BNF,     
       `OR1K_OPCODE_BF,      
       `OR1K_OPCODE_MOVHI,   
       `OR1K_OPCODE_RFE,      
       `OR1K_OPCODE_JR,      
       `OR1K_OPCODE_JALR,
       `OR1K_OPCODE_LWZ,     
       `OR1K_OPCODE_LWS,     
       `OR1K_OPCODE_LBZ,     
       `OR1K_OPCODE_LBS,     
       `OR1K_OPCODE_LHZ,     
       `OR1K_OPCODE_LHS,       
       `OR1K_OPCODE_ADDI,
       `OR1K_OPCODE_ANDI,    
       `OR1K_OPCODE_ORI,     
       `OR1K_OPCODE_XORI,
       `OR1K_OPCODE_MFSPR,   
       /*	    `OR1K_OPCODE_SLLI,    
	`OR1K_OPCODE_SRLI,    
	`OR1K_OPCODE_SRAI,    
	`OR1K_OPCODE_RORI,    
	*/
       `OR1K_OPCODE_SFIMM,   
       `OR1K_OPCODE_MTSPR,
       `OR1K_OPCODE_SW,      
       `OR1K_OPCODE_SB,      
       `OR1K_OPCODE_SH,
       /* 
	`OR1K_OPCODE_SFEQ,    
	`OR1K_OPCODE_SFNE,    
	`OR1K_OPCODE_SFGTU,   
	`OR1K_OPCODE_SFGEU,   
	`OR1K_OPCODE_SFLTU,   
	`OR1K_OPCODE_SFLEU,   
	`OR1K_OPCODE_SFGTS,   
	`OR1K_OPCODE_SFGES,   
	`OR1K_OPCODE_SFLTS,   
	`OR1K_OPCODE_SFLES,
	*/
       `OR1K_OPCODE_SF,
       `OR1K_OPCODE_NOP:
	 execute_except_illegal = 1'b0;

       `OR1K_OPCODE_CUST1:
	 execute_except_illegal = (FEATURE_CUST1=="NONE");
       `OR1K_OPCODE_CUST2:
	 execute_except_illegal = (FEATURE_CUST2=="NONE");
       `OR1K_OPCODE_CUST3:
	 execute_except_illegal = (FEATURE_CUST3=="NONE");
       `OR1K_OPCODE_CUST4:
	 execute_except_illegal = (FEATURE_CUST4=="NONE");
       `OR1K_OPCODE_CUST5:
	 execute_except_illegal = (FEATURE_CUST5=="NONE");
       `OR1K_OPCODE_CUST6:
	 execute_except_illegal = (FEATURE_CUST6=="NONE");
       `OR1K_OPCODE_CUST7:
	 execute_except_illegal = (FEATURE_CUST7=="NONE");
       `OR1K_OPCODE_CUST8:
	 execute_except_illegal = (FEATURE_CUST8=="NONE");

       `OR1K_OPCODE_LD,
	 `OR1K_OPCODE_SD:
	   execute_except_illegal = !(OPTION_OPERAND_WIDTH==64);
       
       `OR1K_OPCODE_ADDIC:
	 execute_except_illegal = (FEATURE_ADDC=="NONE");

       //`OR1K_OPCODE_MACRC, // Same as movhi - check!
       `OR1K_OPCODE_MACI,
	 `OR1K_OPCODE_MAC:
	   execute_except_illegal = (FEATURE_MAC=="NONE");	  
       
       `OR1K_OPCODE_MULI:
	 execute_except_illegal = (FEATURE_MULTIPLIER=="NONE");	  

       `OR1K_OPCODE_SHRTI:
	 case(decode_insn_i[`OR1K_ALU_OPC_SECONDAY_SELECT])
	   `OR1K_ALU_OPC_SECONDARY_SHRT_SLL,
	   `OR1K_ALU_OPC_SECONDARY_SHRT_SRL:
	     execute_except_illegal = 1'b0;
	   `OR1K_ALU_OPC_SECONDARY_SHRT_SRA:
	     execute_except_illegal = (FEATURE_SRA=="NONE");
	   
	   `OR1K_ALU_OPC_SECONDARY_SHRT_ROR:
	     execute_except_illegal = (FEATURE_ROR=="NONE");
	   default:
	     execute_except_illegal = 1'b1;
	 endcase // case (decode_insn_i[`OR1K_ALU_OPC_SECONDAY_SELECT])
       
       `OR1K_OPCODE_ALU:
	 case(decode_insn_i[`OR1K_ALU_OPC_SELECT])
	   `OR1K_ALU_OPC_ADD,
	   `OR1K_ALU_OPC_SUB,     
	   `OR1K_ALU_OPC_OR,      
	   `OR1K_ALU_OPC_XOR,
	   `OR1K_ALU_OPC_AND:
	     execute_except_illegal = 1'b0;
	   `OR1K_ALU_OPC_CMOV:
	     execute_except_illegal = (FEATURE_CMOV=="NONE");
	   `OR1K_ALU_OPC_FFL1:
	     execute_except_illegal = (FEATURE_FFL1=="NONE");	      
	   `OR1K_ALU_OPC_DIV,     
	     `OR1K_ALU_OPC_DIVU:
	       execute_except_illegal = (FEATURE_DIVIDER=="NONE");
	   `OR1K_ALU_OPC_ADDC:
	     execute_except_illegal = (FEATURE_ADDC=="NONE");	  
	   `OR1K_ALU_OPC_MUL,
	     `OR1K_ALU_OPC_MULU:
	       execute_except_illegal = (FEATURE_MULTIPLIER=="NONE");	  
	   `OR1K_ALU_OPC_EXTBH,
	     `OR1K_ALU_OPC_EXTW:
	       execute_except_illegal = (FEATURE_EXT=="NONE");	  
	   `OR1K_ALU_OPC_SHRT:
	     case(decode_insn_i[`OR1K_ALU_OPC_SECONDAY_SELECT])
	       `OR1K_ALU_OPC_SECONDARY_SHRT_SLL,
	       `OR1K_ALU_OPC_SECONDARY_SHRT_SRL:
		 execute_except_illegal = 1'b0;
	       `OR1K_ALU_OPC_SECONDARY_SHRT_SRA:
		 execute_except_illegal = (FEATURE_SRA=="NONE");	  
	       `OR1K_ALU_OPC_SECONDARY_SHRT_ROR:
		 execute_except_illegal = (FEATURE_ROR=="NONE");	  
	       default:
		 execute_except_illegal = 1'b1;
	     endcase // case (decode_insn_i[`OR1K_ALU_OPC_SECONDAY_SELECT])
	   default:
	     execute_except_illegal = 1'b1;
	 endcase // case (decode_insn_i[`OR1K_ALU_OPC_SELECT])

       `OR1K_OPCODE_SYSTRAPSYNC: begin
	  if ((decode_insn_i[`OR1K_SYSTRAPSYNC_OPC_SELECT] ==
	       `OR1K_SYSTRAPSYNC_OPC_SYSCALL && 
	       FEATURE_SYSCALL=="ENABLED") ||
	      (decode_insn_i[`OR1K_SYSTRAPSYNC_OPC_SELECT] ==
	       `OR1K_SYSTRAPSYNC_OPC_TRAP &&
	       FEATURE_TRAP=="ENABLED"))
	    execute_except_illegal = 1'b0;
	  else
	    execute_except_illegal = 1'b1;    
       end // case: endcase...
       default:
	 execute_except_illegal = 1'b1;
       
     endcase // case (decode_insn_i[`OR1K_OPCODE_SELECT])


   
   generate
      if (REGISTERED_DECODE == "ENABLED") begin : registered_decode
	 
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst) begin
	      rf_wb_o <= 0;
	   end
	   else if (padv_i ) begin
	      rf_wb_o <= rf_wb;
	   end
	 
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst) begin
	      op_jbr_o <= 0;
	      op_jr_o <= 0;
	      op_jal_o <= 0;
	   end
	   else if (pipeline_flush_i)
	     begin
		op_jbr_o <= 0;
		op_jr_o <= 0;
		op_jal_o <= 0;
	     end
	   else if (padv_i ) begin
	      op_jbr_o <= op_jbr;
	      op_jr_o <= op_jr;
	      op_jal_o <= op_jal;
	   end
	 
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     op_alu_o <= 1'b0;
	   else if (padv_i )
	     op_alu_o <= op_alu;
	 
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst) 
	     begin
		op_lsu_load_o <= 0;
		op_lsu_store_o <= 0;
	     end
	   else if (pipeline_flush_i) 
	     begin
		op_lsu_load_o <= 0;
		op_lsu_store_o <= 0;
	     end
	   else if (padv_i ) begin
       	      op_lsu_load_o <= op_load;
	      op_lsu_store_o <= op_store;
	   end
	 
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     op_mfspr_o <= 1'b0;
	   else if (padv_i )
	     op_mfspr_o <= op_mfspr;
	 
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     imm16_o <= 0;
	   else if (padv_i)
	     imm16_o <= imm16;
	 
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     immjbr_upper_o <= 0;
	   else if (padv_i )
	     immjbr_upper_o <= immjbr_upper;
	 
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst) begin
	      opc_alu_o <= 0;
	      opc_alu_secondary_o <= 0;
	   end 
	   else if (padv_i ) begin
	      opc_alu_o <= opc_alu;
	      opc_alu_secondary_o <= opc_alu_secondary;
	   end
	 
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     opc_insn_o <= `OR1K_OPCODE_NOP;
	   else if (pipeline_flush_i)
	     opc_insn_o <= `OR1K_OPCODE_NOP;
	   else if (padv_i )
	     opc_insn_o <= opc_insn;
	 
	 // Decode for system call exception
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     execute_except_syscall_o <= 0;
	   else if (padv_i && FEATURE_SYSCALL=="ENABLED")
	     execute_except_syscall_o <= execute_except_syscall;
	 
	 // Decode for system call exception
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     execute_except_trap_o <= 0;
	   else if (padv_i && FEATURE_TRAP=="ENABLED")
	     execute_except_trap_o <= execute_except_trap;
	 
	 // Decode Illegal instruction
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     execute_except_illegal_o <= 0;
	   else if (padv_i )
	     execute_except_illegal_o <= execute_except_illegal;
	 
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     execute_except_ibus_err_o <= 1'b0;
	   else if (padv_i )
	     execute_except_ibus_err_o <= execute_except_ibus_err;
	 
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     decode_valid_o <= 0;
	   else
	     decode_valid_o <= padv_i ;
	 
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     pc_execute_o <= OPTION_RESET_PC;
	   else if (padv_i )
	     pc_execute_o <= pc_execute;   

      end // block: registered_decode
      else begin : combinatorial_decode

	 always @*
	   begin

	      rf_wb_o			= rf_wb;


	      op_jbr_o			= op_jbr;
	      op_jr_o			= op_jr;
	      op_jal_o			= op_jal;
	      
	      

	      op_alu_o			= op_alu;
	      
       	      op_lsu_load_o		= op_load;
	      op_lsu_store_o		= op_store;
	      

	      op_mfspr_o		= op_mfspr;
	      
	      imm16_o			= imm16;
	      
	      
	      immjbr_upper_o		= immjbr_upper;
	      
	      
	      opc_alu_o			= opc_alu;
	      opc_alu_secondary_o	= opc_alu_secondary;
	      
	      opc_insn_o		= opc_insn;
	      
	      execute_except_syscall_o	= execute_except_syscall;
	      
	      execute_except_trap_o	= execute_except_trap;
	      
	      execute_except_illegal_o	= execute_except_illegal;
	      
	      
	      execute_except_ibus_err_o = execute_except_ibus_err;
	      decode_valid_o		= padv_i ;

	      pc_execute_o		= pc_execute;   
	      
	   end
	 
      end
   endgenerate
   
endmodule // mor1kx_decode
