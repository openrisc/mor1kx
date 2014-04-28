`include "mor1kx-defines.v"

`define OR1K_OPCODE_POS 31:26
`define OR1K_J_BR_IMM_POS 25:0
`define OR1K_RD_POS 25:21
`define OR1K_RA_POS 20:16
`define OR1K_RB_POS 15:11
`define OR1K_ALU_OP_POS 3:0
`define OR1K_SF_OP 25:21
`define OR1K_XSYNC_OP_POS 25:21

module mor1kx_traceport_monitor(/*AUTOARG*/
   // Outputs
   finish,
   // Inputs
   clk, rst, traceport_exec_valid, traceport_exec_pc,
   traceport_exec_insn, traceport_exec_wbdata, traceport_exec_wbreg,
   traceport_exec_wben, finish_cross
   );

   parameter OPTION_OPERAND_WIDTH	= 32;
   parameter OPTION_RF_ADDR_WIDTH	= 5;

   parameter LOG_DIR = "../out";

   parameter COREID = 0;
   parameter NUMCORES = 1;

   integer    fgeneral = 0;
   integer    ftrace = 0;
   integer    insns = 0;
   
   input clk;
   input rst;

   input                             traceport_exec_valid;
   input [31:0] 		     traceport_exec_pc;
   input [`OR1K_INSN_WIDTH-1:0]      traceport_exec_insn;
   input [OPTION_OPERAND_WIDTH-1:0]  traceport_exec_wbdata;
   input [OPTION_RF_ADDR_WIDTH-1:0]  traceport_exec_wbreg;
   input 			     traceport_exec_wben;

   input [NUMCORES-1:0] 	     finish_cross;
   output reg 			     finish;

   reg 	TRACE_ENABLE;
   initial TRACE_ENABLE = $test$plusargs("trace_enable");

   reg 	TRACE_TO_SCREEN;
   initial TRACE_TO_SCREEN = $test$plusargs("trace_to_screen");

   reg [63:0] cycle_counter = 0 ;

   reg [OPTION_OPERAND_WIDTH-1:0] r3;
   reg [7:0] 		  printstring [0:255];
   integer 			  printstringpos;
   
   /* Log file management code */
   initial
     begin
	$timeformat (-9, 2, " ns", 12);
//	fgeneral = $fopen({LOG_DIR,"/",`TEST_NAME_STRING,"-general.log"});
//	ftrace = $fopen({LOG_DIR,"/",`TEST_NAME_STRING,"-trace.log"});
	finish = 0;
	printstringpos = 0;
     end

   reg [`OR1K_INSN_WIDTH-1:0]      execute_insn;
   integer 			   i;
   
   always @(negedge clk) begin
      if ((COREID == 0) && &finish_cross) begin
	 $finish;
      end
      
      cycle_counter = cycle_counter + 1;

      if (traceport_exec_valid)
	begin
	  insns = insns + 1;
	  execute_insn = traceport_exec_insn;

	   if (traceport_exec_wben && (traceport_exec_wbreg == 3)) begin
	      r3 = traceport_exec_wbdata;
	   end

/*	   TODO: Re-enable
 if(TRACE_ENABLE)
	     mor1k_trace_print(execute_insn, `CPU_SR, `EXECUTE_PC, `CPU_FLAG);*/
	  
	  // Check instructions for simulation controls
	  if (execute_insn == 32'h15_00_00_01)
	    begin
//	       $fdisplay(fgeneral,"%0t:exit(0x%08h);",$time,r3);
//	       $fdisplay(ftrace,"exit(0x%08h);",r3);
	       $display("[%0d] exit(0x%08h);",COREID,r3);
	       $finish;
	    end
	  if (execute_insn == 32'h15_00_00_02)
	    begin
//	       $fdisplay(fgeneral,"%0t:report(0x%08h);",$time,r3);
//	       $fdisplay(ftrace,"report(0x%08h);",r3);
	       $display("[%0d, %0t] report(0x%08h);",COREID,$time,r3);
	    end
	  if (execute_insn == 32'h15_00_00_04)
	    begin
	       printstring[printstringpos] = r3[7:0];
	       printstringpos = printstringpos + 1;
	       if (r3 == 32'h0a) begin
		  $write("[%0d, %0t] ",COREID,$time);
		  for (i = 0; i < printstringpos; i = i + 1) begin
		     $write("%s",printstring[i]);
		  end
		  printstringpos = 0;
	       end
//	       $fdisplay(fgeneral, "%0t: l.nop putc (%c)", $time,r3);
	    end

	  if (execute_insn == 32'h15_00_00_0c)
	    begin
	       // Silent exit
	       finish = 1;
	    end
	  
       end // if (`EXECUTE_STAGE_ADV)
   end

endmodule // mor1kx_traceport_monitor
