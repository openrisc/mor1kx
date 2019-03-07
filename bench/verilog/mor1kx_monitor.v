/* ****************************************************************************
  This Source Code Form is subject to the terms of the 
  Open Hardware Description License, v. 1.0. If a copy 
  of the OHDL was not distributed with this file, You 
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: mor1kx monitor module
 
  Attaches to hooks provided in the mor1kx pipeline wrapper and provides
  execution trace, disassembly, and l.nop instruction functions.
   
  Copyright (C) 2012, 2013 Authors
 
  Author(s): Julius Baxter <juliusbaxter@gmail.com>
 
***************************************************************************** */

/* Configure these defines to point to the mor1kx instantiation */
`ifndef MOR1KX_INST
 `define MOR1KX_INST dut.mor1kx0
`endif

/* The rest of these shouldn't need changing if the wrapper hooks have been 
 set up correctly in mor1kx_cpu. */
`ifndef CPU_WRAPPER
 `define CPU_WRAPPER `MOR1KX_INST.mor1kx_cpu
`endif
`define EXECUTE_STAGE_INSN `CPU_WRAPPER.monitor_execute_insn
`define EXECUTE_STAGE_ADV `CPU_WRAPPER.monitor_execute_advance
`define CPU_clk `CPU_WRAPPER.monitor_clk
`define CPU_FLAG `CPU_WRAPPER.monitor_flag
`define CPU_SR `CPU_WRAPPER.monitor_spr_sr
`define EXECUTE_PC `CPU_WRAPPER.monitor_execute_pc
`define GPR_GET(x) `CPU_WRAPPER.monitor.get_gpr(x)
`define GPR_SET(x, y) `CPU_WRAPPER.monitor.set_gpr(x, y)

`include "mor1kx-defines.v"

// Pull in an ORPSoC-specific file
`include "test-defines.v" // indicate if we should trace or not

// OR1K ISA defines used in this file

`define OR1K_OPCODE_POS 31:26
`define OR1K_J_BR_IMM_POS 25:0
`define OR1K_RD_POS 25:21
`define OR1K_RA_POS 20:16
`define OR1K_RB_POS 15:11
`define OR1K_ALU_OP_POS 3:0
`define OR1K_SF_OP 25:21
`define OR1K_XSYNC_OP_POS 25:21

module mor1kx_monitor #(parameter LOG_DIR= "../out") ();

   // General output file descriptor
   integer    fgeneral = 0;
   integer    ftrace = 0;
   integer    insns = 0;
   
   wire clk;

   parameter OPTION_OPERAND_WIDTH = 32;
   
   reg 	TRACE_ENABLE;
   initial TRACE_ENABLE = $test$plusargs("trace_enable");

   reg 	TRACE_TO_SCREEN;
   initial TRACE_TO_SCREEN = $test$plusargs("trace_to_screen");

   assign clk = `CPU_clk;

   reg [63:0] cycle_counter = 0 ;
   
   /* Log file management code */
   initial
     begin
	$timeformat (-9, 2, " ns", 12);
	fgeneral = $fopen({LOG_DIR,"/",`TEST_NAME_STRING,"-general.log"});
	ftrace = $fopen({LOG_DIR,"/",`TEST_NAME_STRING,"-trace.log"});
     end
  
   /* Simulation support code */

   reg [1:80*8] decode_insn_disas;
   reg [1:80*8] execute_insn_disas;
   reg [OPTION_OPERAND_WIDTH-1:0] decode_pc;
   reg [OPTION_OPERAND_WIDTH-1:0] execute_pc;
   
   reg [`OR1K_INSN_WIDTH-1:0]      execute_insn;
   reg 				   flag_4stage;
   
   always @(`EXECUTE_STAGE_INSN)
     mor1k_insn_to_string(`EXECUTE_STAGE_INSN, execute_insn_disas);
	  //$write("%tns: decode insn PC %08h %08h %s\n",$time, pc_decode_i, 
          // decode_insn_i, insn_disassembled_string);
   
   always @(negedge `CPU_clk) begin
      
      cycle_counter = cycle_counter + 1;
      
      if (`EXECUTE_STAGE_ADV)
	begin
	  insns = insns + 1;
	  execute_insn = `EXECUTE_STAGE_INSN;

	   if(TRACE_ENABLE)
	     mor1k_trace_print(execute_insn, `CPU_SR, `EXECUTE_PC, `CPU_FLAG);
	  
	  // Check instructions for simulation controls
	  if (execute_insn == 32'h15_00_00_01)
	    begin
	       $fdisplay(fgeneral,"%0t:exit(0x%08h);",$time,`GPR_GET(3));
	       $fdisplay(ftrace,"exit(0x%08h);",`GPR_GET(3));
	       $display("exit(0x%08h);",`GPR_GET(3));
	       $finish;
	    end
	  if (execute_insn == 32'h15_00_00_02)
	    begin
	       $fdisplay(fgeneral,"%0t:report(0x%08h);",$time,`GPR_GET(3));
	       $fdisplay(ftrace,"report(0x%08h);",`GPR_GET(3));
	       $display("report(0x%08h);",`GPR_GET(3));
	    end
	  if (execute_insn == 32'h15_00_00_04)
	    begin
	       $write("%c",`GPR_GET(3));
	       $fdisplay(fgeneral, "%0t: l.nop putc (%c)", $time,`GPR_GET(3));
	    end
	  if (execute_insn == 32'h15_00_00_05)
	    begin
	       cycle_counter = 0;
	       $fdisplay(fgeneral, "%0t: l.nop reset counter", $time);
	    end
	   if (execute_insn == 32'h15_00_00_06)
	     begin
		$fdisplay(fgeneral, "%0t: l.nop report cycle counter: %d", $time, cycle_counter);
		`GPR_SET(11,cycle_counter[31:0]);
		`GPR_SET(12,cycle_counter[63:32]);
	    end	   

	  if (execute_insn == 32'h15_00_00_0c)
	    begin
	       // Silent exit
	       $finish;
	       
	    end
	  
       end // if (`EXECUTE_STAGE_ADV)
   end
   
   task mor1k_trace_print;
      input [31:0] insn;
      input [31:0] sr;
      input [31:0] pc;
      input 	   flag;
      
      
      reg 	   rD_used;
      reg [4:0]    rD_num, rA_num, rB_num;
      reg [15:0]   imm_16bit;
      reg [25:0]   imm_26bit;
      reg [31:0]   signext_imm_16bit;
      
      reg [1:80*8] insn_disas;
      // Actual things happening
      reg [15:0]   regimm_chars;
      reg [31:0]   addr_result;
      begin

	 // Get instruction info
	 mor1kx_insn_info(insn,rA_num,rB_num,rD_num,rD_used,imm_16bit, 
			  imm_26bit,regimm_chars);

	 /* Sign-extend the 16-bit immediate to 32-bit so we can add it to other
	  32-bit numbers and it should subtract if necessary */
	 signext_imm_16bit = {{16{imm_16bit[15]}},imm_16bit};
	 
	 // Display useful line of stuff, like or1ksim trace
	 if (sr[`OR1K_SPR_SR_SM] === 1'b0)
	   begin
	      $fwrite(ftrace,"U ");
	      if(TRACE_TO_SCREEN)
		$write("U ");
	   end
	 else
	   begin
	      $fwrite(ftrace,"S ");
	      if(TRACE_TO_SCREEN)
		$write("S ");
	   end
	 
	 // PC next
	 $fwrite(ftrace,"%08h: ", pc);
	 if(TRACE_TO_SCREEN)
	   $write("%08h: ", pc);
	 
	 // Instruction raw
	 $fwrite(ftrace,"%08h ",insn);
	 if(TRACE_TO_SCREEN)
	   $write("%08h ",insn);
	 
	 mor1k_insn_to_string(insn, insn_disas);
	 
	 // Instruction, disassembled
	 $fwrite(ftrace,"%0s", insn_disas);
	 if(TRACE_TO_SCREEN)
	   $write("%0s", insn_disas);
	 
	 for (regimm_chars=regimm_chars;
	      regimm_chars < 16; regimm_chars = regimm_chars + 1)
	   begin
	      $fwrite(ftrace," ");
	      if(TRACE_TO_SCREEN)
		$write(" ");
	   end
	 
	 if (rD_used)
	   begin
	      if (insn[`OR1K_OPCODE_SELECT]===`OR1K_OPCODE_MFSPR)
		begin
		   // Wait 1 cycle for MFSPR result
		   @(posedge `CPU_clk);
		   $fwrite(ftrace,"r%0d",rD_num);
		   if(TRACE_TO_SCREEN)
		     $write("r%0d",rD_num);
		end
	      else
		begin
		   $fwrite(ftrace,"r%0d",rD_num);
		   if(TRACE_TO_SCREEN)
		     $write("r%0d",rD_num);
		end // else: !if(insn[`OR1K_OPCODE_SELECT]===`OR1K_OPCODE_MFSPR)

	      // Tab 1 more if we're a single-number register 
	      if (rD_num < 10) begin
		 $fwrite(ftrace,"\t\t");
		 if(TRACE_TO_SCREEN)
		   $write("\t\t");
	      end
	      else begin
		 $fwrite(ftrace,"\t");
		 if(TRACE_TO_SCREEN)
		   $write("\t");
	      end
	      
	      // Finally write what ended up in the in rD
	      $fwrite(ftrace,"= %08h  ",`GPR_GET(rD_num));
	      if(TRACE_TO_SCREEN)
		$write("= %08h  ",`GPR_GET(rD_num));
	   end
	 else if (insn[`OR1K_OPCODE_SELECT]===`OR1K_OPCODE_MTSPR)
	   begin
	      // Clobber imm_16bit here to calculate MTSPR
	      imm_16bit = imm_16bit | `GPR_GET(rA_num);
	      $fwrite(ftrace,"SPR[%04x]  = %08h  ", imm_16bit, `GPR_GET(rB_num));
	      if(TRACE_TO_SCREEN)
		$write("SPR[%04x]  = %08h  ", imm_16bit, `GPR_GET(rB_num));
	      
	   end // if (insn[`OR1K_OPCODE_SELECT]===`OR1K_OPCODE_MTSPR)
	 else if (insn[`OR1K_OPCODE_SELECT]>=`OR1K_OPCODE_SD &&
		  insn[`OR1K_OPCODE_SELECT]<=`OR1K_OPCODE_SH)
	   begin
	      addr_result = signext_imm_16bit + `GPR_GET(rA_num);
	      $fwrite(ftrace,"[%08h] = %08h  ",addr_result[31:0],
		     `GPR_GET(rB_num));
	      if(TRACE_TO_SCREEN)
		$write("[%08h] = %08h  ",addr_result[31:0],
		       `GPR_GET(rB_num));
	   end
	 else
	   begin
	      // Skip destination field
	      $fwrite(ftrace,"\t\t\t    ");
	      if(TRACE_TO_SCREEN)
		$write("\t\t\t    ");
	   end

	 /* Write flag */
	 $fwrite(ftrace,"flag: %0d", flag);
	 if(TRACE_TO_SCREEN)
	   $write("flag: %0d", flag);

	 /* End of line */
	 $fwrite(ftrace,"\n");
	 if(TRACE_TO_SCREEN)
	   $write("\n");
	 
      end
   endtask // mor1k_trace_print

   task mor1kx_insn_info;
      input [31:0] insn;
      output [4:0] rA_num;
      output [4:0] rB_num;
      output [4:0] rD_num;
      output 	   rD_used;
      output [15:0] imm_16bit;
      output [25:0] imm_26bit;
      
      output [7:0]  num_chars;

      // To count how long disassembled immediates/regs
      // are - what a pain!
      reg 	    rA_used, rB_used, imm_16bit_used,
		    imm_26bit_used;
      
      reg [5:0]     opcode;

      reg 	    opc_store;
      
      begin

	 // Register numbers (D, A and B)
	 rD_num = insn[`OR1K_RD_POS];
	 rA_num = insn[`OR1K_RA_POS];	 
	 rB_num = insn[`OR1K_RB_POS];
	 
	 opcode = insn[`OR1K_OPCODE_POS];


	 opc_store = (opcode==`OR1K_OPCODE_SD) ||
		     (opcode==`OR1K_OPCODE_SW) ||
		     (opcode==`OR1K_OPCODE_SB) ||
		     (opcode==`OR1K_OPCODE_SH);
	 
	 case (opcode)
	   `OR1K_OPCODE_LWZ,
	     `OR1K_OPCODE_LBZ,
	     `OR1K_OPCODE_LBS,
	     `OR1K_OPCODE_LHZ,
	     `OR1K_OPCODE_LHS,
	     `OR1K_OPCODE_MFSPR,
	     `OR1K_OPCODE_MOVHI,
	     `OR1K_OPCODE_ADDI,
	     `OR1K_OPCODE_ADDIC,
	     `OR1K_OPCODE_ANDI,
	     `OR1K_OPCODE_ORI,
	     `OR1K_OPCODE_XORI,
	     `OR1K_OPCODE_MULI,
	     `OR1K_OPCODE_ALU,
	     `OR1K_OPCODE_SHRTI:
	       rD_used = 1;
	   default:
	     rD_used=0;
	 endcase // case (opcode)

	 case (opcode)
	   `OR1K_OPCODE_J    ,
	     `OR1K_OPCODE_JAL  ,
	     `OR1K_OPCODE_BNF  ,
	     `OR1K_OPCODE_BF   ,
	     `OR1K_OPCODE_NOP  ,
	     `OR1K_OPCODE_MOVHI,
	     `OR1K_OPCODE_MACRC,
	     `OR1K_OPCODE_SYSTRAPSYNC,
	     `OR1K_OPCODE_RFE,
	     `OR1K_OPCODE_JR,
	     `OR1K_OPCODE_JALR:
	     /*
	      rD of store insns, is in rA field
	     `OR1K_OPCODE_SD,
	     `OR1K_OPCODE_SW,
	     `OR1K_OPCODE_SB,
	     `OR1K_OPCODE_SH
	      */
	       rA_used = 0;
	   default:
	     rA_used=1;
	 endcase // case (opcode)

	 case (opcode)
	   `OR1K_OPCODE_JR,
	     `OR1K_OPCODE_JALR,
	     `OR1K_OPCODE_MTSPR,
	     `OR1K_OPCODE_MAC,
	     `OR1K_OPCODE_MSB,
	     `OR1K_OPCODE_SD,
	     `OR1K_OPCODE_SW,
	     `OR1K_OPCODE_SB,
	     `OR1K_OPCODE_SH,
	     `OR1K_OPCODE_SF:
	       rB_used = 1;
	   `OR1K_OPCODE_ALU:
	     case(insn[`OR1K_ALU_OPC_SELECT])
	       `OR1K_ALU_OPC_EXTBH,
		 `OR1K_ALU_OPC_EXTW,
		 `OR1K_ALU_OPC_FFL1:
		   rB_used = 0;
	       default:
		 rB_used = 1;
	     endcase // case (insn[`OR1K_ALU_OPC_SELECT])
	   default:
	     rB_used = 0;
	 endcase // case (opcode)

	 case (opcode)
	   `OR1K_OPCODE_MOVHI,
	     `OR1K_OPCODE_NOP,
	     `OR1K_OPCODE_SD,
	     `OR1K_OPCODE_SW,
	     `OR1K_OPCODE_SB,
	     `OR1K_OPCODE_SH,
	     `OR1K_OPCODE_LD   ,
	     `OR1K_OPCODE_LWZ  ,
	     `OR1K_OPCODE_LWS  ,
	     `OR1K_OPCODE_LBZ  ,
	     `OR1K_OPCODE_LBS  ,
	     `OR1K_OPCODE_LHZ  ,
	     `OR1K_OPCODE_LHS  ,
	     `OR1K_OPCODE_ADDI ,
	     `OR1K_OPCODE_ADDIC,
	     `OR1K_OPCODE_ANDI ,
	     `OR1K_OPCODE_ORI  ,
	     `OR1K_OPCODE_XORI ,
	     `OR1K_OPCODE_MULI ,
	     `OR1K_OPCODE_MACI ,
	     `OR1K_OPCODE_SFIMM,
	     `OR1K_OPCODE_MTSPR,
	     `OR1K_OPCODE_MFSPR:
	       imm_16bit_used = 1;
	   default:
	     imm_16bit_used = 0;
	 endcase // case (opcode)

	 case (opcode)
	   `OR1K_OPCODE_J  ,
	     `OR1K_OPCODE_JAL,
	     `OR1K_OPCODE_BNF,
	     `OR1K_OPCODE_BF:
	       imm_26bit_used = 1;
	   default:
	     imm_26bit_used = 0;
	 endcase
	 
	 // Extract immediate
	 case (opcode)
	   `OR1K_OPCODE_SW,
	     `OR1K_OPCODE_SB,
	     `OR1K_OPCODE_SH,
	     `OR1K_OPCODE_SD,
	     `OR1K_OPCODE_MTSPR:
	       imm_16bit = {insn[25:21],insn[10:0]};
	   default:
	     imm_16bit = insn[15:0];
	 endcase // case (opcode)

	 imm_26bit = insn[25:0];

	 // Extra chars (commas, brackets)
	 case (opcode)
/*	   
	   `OR1K_OPCODE_J    :
	     num_chars = 0;
	   `OR1K_OPCODE_JAL  :
	     num_chars = 0;
	   `OR1K_OPCODE_BNF  :
	     num_chars = 0;
	   `OR1K_OPCODE_BF   :
	     num_chars = 0;
	   `OR1K_OPCODE_MACRC:
	     num_chars = 0;
	   `OR1K_OPCODE_SYSTRAPSYNC:
	     num_chars = 0;
	   `OR1K_OPCODE_RFE:
	     num_chars = 0;
	   `OR1K_OPCODE_JR   :
	     num_chars = 0;
	   `OR1K_OPCODE_JALR :
	     num_chars = 0;
	   `OR1K_OPCODE_CUST1:
	     num_chars = 0;
	   `OR1K_OPCODE_CUST2:
	     num_chars = 0;
	   `OR1K_OPCODE_CUST3:
	     num_chars = 0;
	   `OR1K_OPCODE_CUST4:
	     num_chars = 0; 
	   `OR1K_OPCODE_NOP  :
	     num_chars = 0; 
 */ 
	   `OR1K_OPCODE_MOVHI:
	     num_chars = 1;
	   `OR1K_OPCODE_MACI :
	     num_chars = 1;
	   `OR1K_OPCODE_LD   :
	     num_chars = 3;
	   `OR1K_OPCODE_LWZ  :
	     num_chars = 3;
	   `OR1K_OPCODE_LWS  :
	     num_chars = 3;
	   `OR1K_OPCODE_LBZ  :
	     num_chars = 3;
	   `OR1K_OPCODE_LBS  :
	     num_chars = 3;
	   `OR1K_OPCODE_LHZ  :
	     num_chars = 3;
	   `OR1K_OPCODE_LHS  :
	     num_chars = 3;
	   `OR1K_OPCODE_ADDI :
	     num_chars = 2;
	   `OR1K_OPCODE_ADDIC:
	     num_chars = 2;
	   `OR1K_OPCODE_ANDI :
	     num_chars = 2;
	   `OR1K_OPCODE_ORI  :
	     num_chars = 2;
	   `OR1K_OPCODE_XORI :
	     num_chars = 2;
	   `OR1K_OPCODE_MULI :
	     num_chars = 2;
	   `OR1K_OPCODE_MFSPR:
	     num_chars = 2;
	   `OR1K_OPCODE_SFIMM:
	     num_chars = 1;
	   `OR1K_OPCODE_MTSPR  :
	     num_chars = 2;
	   `OR1K_OPCODE_MAC    :
	     num_chars = 1;
	   `OR1K_OPCODE_MSB  :
	     num_chars = 1;
	   `OR1K_OPCODE_SD   :
	     num_chars = 3;
	   `OR1K_OPCODE_SW   :
	     num_chars = 3;
	   `OR1K_OPCODE_SB   :
	     num_chars = 3;
	   `OR1K_OPCODE_SH:
	     num_chars = 3;
	   `OR1K_OPCODE_ALU:
	     case(insn[`OR1K_ALU_OPC_SELECT])
	       `OR1K_ALU_OPC_EXTBH,
		 `OR1K_ALU_OPC_EXTW,
		 `OR1K_ALU_OPC_FFL1:
		   num_chars = 1;
	       default:
		 num_chars = 2;
	     endcase // case (insn[`OR1K_ALU_OPC_SELECT])
	   `OR1K_OPCODE_SF:
	     num_chars =1;
	   `OR1K_OPCODE_SHRTI:
	     /*
	     if (insn[5:0] < 6'h10)
	       num_chars = 5;
	     else
	      */
	       num_chars = 6;

	   default:
	     num_chars = 0;
	   
	 endcase // case (opcode)


	 // Determine length of register/immediate
	 // disassembly in characters
	 if (rA_used)
	   num_chars = (rA_num > 9) ? num_chars + 3 :
		       num_chars + 2;
	 
	 if (rB_used)
	   num_chars = (rB_num > 9) ? num_chars + 3 :
		       num_chars + 2;
	 
	 if (rD_used)
	   num_chars = (rD_num > 9) ? num_chars + 3 :
		       num_chars + 2;
	 
	 if (imm_16bit_used)
	   num_chars = num_chars + 6;

	 if (imm_26bit_used)
	   num_chars = num_chars + 9;

	 /*
	 $write("%b %b %b %b %b\n",rA_used, rB_used, rD_used, imm_16bit_used,
		imm_26bit_used);
	  */
	 //$write("%0d\n",num_chars);
      
      end
   endtask // mor1k_insn_info
   
     

   

   task mor1k_insn_to_string;
      input [31:0] insn;
      output [80*8:1] insnstring;

      reg [5:0]    opcode;
      
      reg [25:0]   j_imm;

      reg [25:0]   br_imm;

      reg [31:0]   rA_val, rB_val;
      
      reg [3:0]    alu_op;
      
      reg [5:0]    sf_op;
      
      reg [5:0]    xsync_op;
      
      reg [4:0]    rD_num, rA_num, rB_num;
      
      reg [15:0]   imm_16bit;
      reg [15:0]   imm_split16bit;      
      
      
      begin

	 // Instruction opcode
	 opcode = insn[`OR1K_OPCODE_POS];
	 // Immediates for jump or branch instructions
	 j_imm = insn[`OR1K_J_BR_IMM_POS];
	 br_imm = insn[`OR1K_J_BR_IMM_POS];
	 // Register numbers (D, A and B)
	 rD_num = insn[`OR1K_RD_POS];
	 rA_num = insn[`OR1K_RA_POS];	 
	 rB_num = insn[`OR1K_RB_POS];
	 // Bottom 16 bits when used as immediates in various instructions
	 imm_16bit = insn[15:0];
	 // Bottom 11 bits used as immediates for l.sX instructions

	 // Split 16-bit immediate for l.mtspr/l.sX instructions
	 imm_split16bit = {insn[25:21],insn[10:0]};
	 // ALU op for ALU instructions
	 alu_op = insn[`OR1K_ALU_OP_POS];


	 // Set flag op
	 sf_op = insn[`OR1K_SF_OP];
	 
	 // Xsync/syscall/trap opcode
	 xsync_op = insn[`OR1K_XSYNC_OP_POS];
	 
	 case (opcode)
	   `OR1K_OPCODE_J:
	     begin	      
		$sformat(insnstring, "l.j     0x%07h", j_imm);	      
	     end
	   
	   `OR1K_OPCODE_JAL:
	     begin
		$sformat(insnstring, "l.jal   0x%07h", j_imm);
	     end

	   `OR1K_OPCODE_BNF:
	     begin
		$sformat(insnstring, "l.bnf   0x%07h", br_imm);
	     end
	   
	   `OR1K_OPCODE_BF:
	     begin
		$sformat(insnstring, "l.bf    0x%07h", br_imm);
	     end
	   
	   `OR1K_OPCODE_RFE:
	     begin
		$sformat(insnstring, "l.rfe   ");	      
	     end
	   
	   `OR1K_OPCODE_JR:
	     begin
		$sformat(insnstring, "l.jr    r%0d",rB_num);
	     end
	   
	   `OR1K_OPCODE_JALR:
	     begin
		$sformat(insnstring, "l.jalr  r%0d",rB_num);
	     end
	   
	   `OR1K_OPCODE_LWZ:
	     begin
		$sformat(insnstring, "l.lwz   r%0d,0x%04h(r%0d)",rD_num,imm_16bit,rA_num);
	     end
	   
	   `OR1K_OPCODE_LBZ:
	     begin
		$sformat(insnstring, "l.lbz   r%0d,0x%04h(r%0d)",rD_num,imm_16bit,rA_num);
	     end
	   
	   `OR1K_OPCODE_LBS:
	     begin
		$sformat(insnstring, "l.lbs   r%0d,0x%04h(r%0d)",rD_num,imm_16bit,rA_num);
	     end
	   
	   `OR1K_OPCODE_LHZ:
	     begin
		$sformat(insnstring, "l.lhz   r%0d,0x%04h(r%0d)",rD_num,imm_16bit,rA_num);
	     end
	   
	   `OR1K_OPCODE_LHS:
	     begin
		$sformat(insnstring, "l.lhs   r%0d,0x%04h(r%0d)",rD_num,imm_16bit,rA_num);
	     end
	   
	   `OR1K_OPCODE_SW:
	     begin
		$sformat(insnstring, "l.sw    0x%04h(r%0d),r%0d",imm_split16bit,rA_num,rB_num);
	     end
	   
	   `OR1K_OPCODE_SB:
	     begin
		$sformat(insnstring, "l.sb    0x%04h(r%0d),r%0d",imm_split16bit,rA_num,rB_num);
	     end
	   
	   `OR1K_OPCODE_SH:
	     begin
		$sformat(insnstring, "l.sh    0x%04h(r%0d),r%0d",imm_split16bit,rA_num,rB_num);	      
	     end
	   
	   `OR1K_OPCODE_MFSPR:
	     begin
		$sformat(insnstring, "l.mfspr r%0d,r%0d,0x%04h",rD_num,rA_num,imm_16bit);
	     end	      

	   `OR1K_OPCODE_MTSPR:
	     begin
		$sformat(insnstring, "l.mtspr r%0d,r%0d,0x%04h",rA_num,rB_num,imm_split16bit);	
	     end
	   
	   `OR1K_OPCODE_MOVHI:
	     begin
		if (!insn[16])begin
		   $sformat(insnstring, "l.movhi r%0d,0x%04h",rD_num,imm_16bit);
		end
		else
		  $sformat(insnstring, "l.macrc r%0d",rD_num);
	     end
	   
	   `OR1K_OPCODE_ADDI:
	     begin
		$sformat(insnstring, "l.addi  r%0d,r%0d,0x%04h",rD_num,rA_num,imm_16bit);
	     end
	   
	   `OR1K_OPCODE_ADDIC:
	     begin
		$sformat(insnstring, "l.addic r%0d,r%0d,0x%04h",rD_num,rA_num,imm_16bit);
	     end
	   
	   `OR1K_OPCODE_ANDI:
	     begin
		$sformat(insnstring, "l.andi  r%0d,r%0d,0x%04h",rD_num,rA_num,imm_16bit);
	     end	     
	   
	   `OR1K_OPCODE_ORI:
	     begin
		$sformat(insnstring, "l.ori   r%0d,r%0d,0x%04h",rD_num,rA_num,imm_16bit);
	     end	     

	   `OR1K_OPCODE_XORI:
	     begin
		$sformat(insnstring, "l.xori  r%0d,r%0d,0x%04h",rD_num,rA_num,imm_16bit);
	     end	     

	   `OR1K_OPCODE_MULI:
	     begin
		$sformat(insnstring, "l.muli  r%0d,r%0d,0x%04h",rD_num,rA_num,imm_16bit);
	     end
	   
	   `OR1K_OPCODE_ALU:
	     begin
		case(insn[`OR1K_ALU_OPC_SELECT])
		  `OR1K_ALU_OPC_ADD:
		    $sformat(insnstring, "l.add   r%0d,r%0d,r%0d",rD_num,rA_num,rB_num); 
		  `OR1K_ALU_OPC_ADDC:
		    $sformat(insnstring, "l.addc  r%0d,r%0d,r%0d",rD_num,rA_num,rB_num); 
		  `OR1K_ALU_OPC_SUB:
		    $sformat(insnstring, "l.sub   r%0d,r%0d,r%0d",rD_num,rA_num,rB_num);
		  `OR1K_ALU_OPC_AND:
		    $sformat(insnstring, "l.and   r%0d,r%0d,r%0d",rD_num,rA_num,rB_num); 
		  `OR1K_ALU_OPC_OR:
		    $sformat(insnstring, "l.or    r%0d,r%0d,r%0d",rD_num,rA_num,rB_num); 
		  `OR1K_ALU_OPC_XOR:
		    $sformat(insnstring, "l.xor   r%0d,r%0d,r%0d",rD_num,rA_num,rB_num); 
		  `OR1K_ALU_OPC_MUL:
		    $sformat(insnstring, "l.mul   r%0d,r%0d,r%0d",rD_num,rA_num,rB_num); 
		  `OR1K_ALU_OPC_SHRT:
		    begin
		       case(insn[`OR1K_ALU_OPC_SECONDARY_SELECT])
			 `OR1K_ALU_OPC_SECONDARY_SHRT_SLL:
			   $sformat(insnstring, "l.sll   r%0d,r%0d,r%0d",rD_num,rA_num,rB_num);
			 `OR1K_ALU_OPC_SECONDARY_SHRT_SRL:
			   $sformat(insnstring, "l.srl   r%0d,r%0d,r%0d",rD_num,rA_num,rB_num);
			 `OR1K_ALU_OPC_SECONDARY_SHRT_SRA:
			   $sformat(insnstring, "l.sra   r%0d,r%0d,r%0d",rD_num,rA_num,rB_num);
			 `OR1K_ALU_OPC_SECONDARY_SHRT_ROR:
			   $sformat(insnstring, "l.ror   r%0d,r%0d,r%0d",rD_num,rA_num,rB_num);
		       endcase // case (insn[`OR1K_ALU_OPC_SECONDARY_SELECT])
		    end
		  `OR1K_ALU_OPC_DIV:
		    $sformat(insnstring, "l.div   r%0d,r%0d,r%0d",rD_num,rA_num,rB_num); 
		  `OR1K_ALU_OPC_DIVU:
		    $sformat(insnstring, "l.divu  r%0d,r%0d,r%0d",rD_num,rA_num,rB_num);
		  `OR1K_ALU_OPC_MULU:
		    $sformat(insnstring, "l.mulu  r%0d,r%0d,r%0d",rD_num,rA_num,rB_num);		  
		  `OR1K_ALU_OPC_CMOV:
		    $sformat(insnstring, "l.cmov  r%0d,r%0d,r%0d",rD_num,rA_num,rB_num);
		  `OR1K_ALU_OPC_FFL1:
		    begin
		       case(insn[8])
			 0:
			   $sformat(insnstring, "l.ff1   r%0d,r%0d",rD_num,rA_num);
			 1:
			   $sformat(insnstring, "l.fl1   r%0d,r%0d",rD_num,rA_num);
		       endcase // case (insn[8])
		    end
		    
		endcase // case (alu_op)
		//$sformat(insnstring, "r%0d,r%0d,r%0d",rD_num,rA_num,rB_num);
	     end
	   
	   `OR1K_OPCODE_SHRTI:
	     begin
		case(insn[`OR1K_ALU_OPC_SECONDARY_SELECT])
		  `OR1K_ALU_OPC_SECONDARY_SHRT_SLL:
		    $sformat(insnstring, "l.slli  r%0d,r%0d,0x%01h",rD_num,rA_num,insn[5:0]);
		  `OR1K_ALU_OPC_SECONDARY_SHRT_SRL:
		    $sformat(insnstring, "l.srli  r%0d,r%0d,0x%01h",rD_num,rA_num,insn[5:0]);
		  `OR1K_ALU_OPC_SECONDARY_SHRT_SRA:
		    $sformat(insnstring, "l.srai  r%0d,r%0d,0x%01h",rD_num,rA_num,insn[5:0]);
		  `OR1K_ALU_OPC_SECONDARY_SHRT_ROR:
		    $sformat(insnstring, "l.rori  r%0d,r%0d,0x%01h",rD_num,rA_num,insn[5:0]);		  
		endcase // case (insn[`OR1K_ALU_OPC_SECONDARY_SELECT])
		//$sformat(insnstring, "r%0d,r%0d,0x%0h",rD_num,rA_num,insn[5:0]);				
	     end // case: `OR1K_OPCODE_SHRTI
	   
	   `OR1K_OPCODE_SFIMM:
	     begin
		case(insn[`OR1K_COMP_OPC_SELECT])
		  `OR1K_COMP_OPC_EQ:
		    $sformat(insnstring, "l.sfeqi r%0d,0x%04h",rA_num, imm_16bit);
		  `OR1K_COMP_OPC_NE:
		    $sformat(insnstring, "l.sfnei r%0d,0x%04h",rA_num, imm_16bit);
		  `OR1K_COMP_OPC_GTU:
		    $sformat(insnstring, "l.sfgtuir%0d,0x%04h",rA_num, imm_16bit);
		  `OR1K_COMP_OPC_GEU:
		    $sformat(insnstring, "l.sfgeuir%0d,0x%04h",rA_num, imm_16bit);
		  `OR1K_COMP_OPC_LTU:
		    $sformat(insnstring, "l.sfltuir%0d,0x%04h",rA_num, imm_16bit);
		  `OR1K_COMP_OPC_LEU:
		    $sformat(insnstring, "l.sfleuir%0d,0x%04h",rA_num, imm_16bit);
		  `OR1K_COMP_OPC_GTS:
		    $sformat(insnstring, "l.sfgtsir%0d,0x%04h",rA_num, imm_16bit);
		  `OR1K_COMP_OPC_GES:
		    $sformat(insnstring, "l.sfgesir%0d,0x%04h",rA_num, imm_16bit); 
		  `OR1K_COMP_OPC_LTS:
		    $sformat(insnstring, "l.sfltsir%0d,0x%04h",rA_num, imm_16bit);
		  `OR1K_COMP_OPC_LES:
		    $sformat(insnstring, "l.sflesir%0d,0x%04h",rA_num, imm_16bit);
		endcase // case (sf_op[2:0])
		
		//$sformat(insnstring, "r%0d,0x%0h",rA_num, imm_16bit);
		
	     end // case: `OR1K_OPCODE_SFXXI

	   `OR1K_OPCODE_SF:
	     begin
		case(insn[`OR1K_COMP_OPC_SELECT])
		  `OR1K_COMP_OPC_EQ:
		    $sformat(insnstring, "l.sfeq  r%0d,r%0d",rA_num, rB_num);
		  `OR1K_COMP_OPC_NE:
		    $sformat(insnstring, "l.sfne  r%0d,r%0d",rA_num, rB_num);
		  `OR1K_COMP_OPC_GTU:
		    $sformat(insnstring, "l.sfgtu r%0d,r%0d",rA_num, rB_num);
		  `OR1K_COMP_OPC_GEU:
		    $sformat(insnstring, "l.sfgeu r%0d,r%0d",rA_num, rB_num);
		  `OR1K_COMP_OPC_LTU:
		    $sformat(insnstring, "l.sfltu r%0d,r%0d",rA_num, rB_num);
		  `OR1K_COMP_OPC_LEU:
		    $sformat(insnstring, "l.sfleu r%0d,r%0d",rA_num, rB_num);
		  `OR1K_COMP_OPC_GTS:
		    $sformat(insnstring, "l.sfgts r%0d,r%0d",rA_num, rB_num);
		  `OR1K_COMP_OPC_GES:
		    $sformat(insnstring, "l.sfges r%0d,r%0d",rA_num, rB_num); 
		  `OR1K_COMP_OPC_LTS:
		    $sformat(insnstring, "l.sflts r%0d,r%0d",rA_num, rB_num);
		  `OR1K_COMP_OPC_LES:
		    $sformat(insnstring, "l.sfles r%0d,r%0d",rA_num, rB_num);
		endcase // case (sf_op[2:0])
		//$sformat(insnstring, "r%0d,r%0d",rA_num, rB_num);
		
	     end
	   
	   `OR1K_OPCODE_MACI:
	     begin
		$sformat(insnstring, "l.maci r%0d,0x%04h",rA_num,imm_16bit);
	     end
	   
	   `OR1K_OPCODE_NOP:
	     begin
		$sformat(insnstring, "l.nop   0x%04h",imm_16bit);
	     end

	   `OR1K_OPCODE_SYSTRAPSYNC:
	     begin
		case (insn[`OR1K_SYSTRAPSYNC_OPC_SELECT])
		  `OR1K_SYSTRAPSYNC_OPC_SYSCALL:
		    $sformat(insnstring, "l.sys   0x%04h",imm_16bit);
		  `OR1K_SYSTRAPSYNC_OPC_TRAP:
		    $sformat(insnstring, "l.trap  0x%04h",imm_16bit);
		  `OR1K_SYSTRAPSYNC_OPC_MSYNC:
		    $sformat(insnstring, "l.msync");
		  `OR1K_SYSTRAPSYNC_OPC_PSYNC:
		    $sformat(insnstring, "l.psync");
		  `OR1K_SYSTRAPSYNC_OPC_CSYNC:
		    $sformat(insnstring, "l.csync");
		endcase // case (insn[`OR1K_SYSTRAPSYNC_OPC_SELECT])
	     end
       `OR1K_OPCODE_FPU:
         begin
             case (insn[`OR1K_FPUOP_SELECT])
                 `OR1K_FPUOP_ADD:
                  $sformat(insnstring, "lf.add.s   r%0d,r%0d,r%0d",rD_num,rA_num,rB_num);
                 `OR1K_FPUOP_SUB:
                  $sformat(insnstring, "lf.sub.s   r%0d,r%0d,r%0d",rD_num,rA_num,rB_num);
                 `OR1K_FPUOP_MUL:
                  $sformat(insnstring, "lf.mul.s   r%0d,r%0d,r%0d",rD_num,rA_num,rB_num);
                 `OR1K_FPUOP_DIV:
                  $sformat(insnstring, "lf.div.s   r%0d,r%0d,r%0d",rD_num,rA_num,rB_num);
                 `OR1K_FPUOP_ITOF:
                  $sformat(insnstring, "lf.itof.s  r%0d,r%0d",rD_num,rA_num);
                 `OR1K_FPUOP_FTOI:
                  $sformat(insnstring, "lf.ftoi.s  r%0d,r%0d",rD_num,rA_num);
                 `OR1K_FPUOP_REM:
                  $sformat(insnstring, "lf.rem.s   r%0d,r%0d,r%0d",rD_num,rA_num,rB_num);
                 `OR1K_FPCOP_SFEQ:
                  $sformat(insnstring, "lf.sfeq.s   r%0d,r%0d",rA_num,rB_num);
                 `OR1K_FPCOP_SFNE:
                  $sformat(insnstring, "lf.sfne.s   r%0d,r%0d",rA_num,rB_num);
                 `OR1K_FPCOP_SFGT:
                  $sformat(insnstring, "lf.sfgt.s   r%0d,r%0d",rA_num,rB_num);
                 `OR1K_FPCOP_SFGE:
                  $sformat(insnstring, "lf.sfge.s   r%0d,r%0d",rA_num,rB_num);
                 `OR1K_FPCOP_SFLT:
                  $sformat(insnstring, "lf.sflt.s   r%0d,r%0d",rA_num,rB_num);
                 `OR1K_FPCOP_SFLE:
                  $sformat(insnstring, "lf.sfle.s   r%0d,r%0d",rA_num,rB_num);
                 default:
                  $sformat(insnstring, "%t: FPU opcode 0x%0h, r%0d,r%0d,r%0d", $time, opcode, rD_num,rA_num,rB_num);
             endcase // case(insn[`OR1K_FPUOP_SELECT])
         end
	   default:
	     begin
		$sformat(insnstring, "%t: Unknown opcode 0x%0h",$time,opcode);
		$sformat(insnstring, "%t: Unknown opcode 0x%0h",$time,opcode);
	     end
	   
	 endcase // case (opcode)
	 
      end
   endtask // mor1k_insn_to_string

endmodule // mor1kx_module
