/* ****************************************************************************
  This Source Code Form is subject to the terms of the 
  Open Hardware Description License, v. 1.0. If a copy 
  of the OHDL was not distributed with this file, You 
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description:  Load, store unit for espresso pipeline
  
  All combinatorial outputs to pipeline
  Dbus interface request signal out synchronous
  
  32-bit specific due to sign extension of results
 
  Copyright (C) 2012 Authors
 
  Author(s): Julius Baxter <juliusbaxter@gmail.com>
 
***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_lsu_espresso
  (/*AUTOARG*/
   // Outputs
   lsu_result_o, lsu_valid_o, lsu_except_dbus_o, lsu_except_align_o,
   dbus_adr_o, dbus_req_o, dbus_dat_o, dbus_bsel_o, dbus_we_o,
   // Inputs
   clk, rst, padv_fetch_i, alu_result_i, rfb_i, opc_insn_i,
   op_lsu_load_i, op_lsu_store_i, exception_taken_i, du_restart_i,
   stepping_i, next_fetch_done_i, dbus_err_i, dbus_ack_i, dbus_dat_i
   );

   parameter OPTION_OPERAND_WIDTH = 32;
   
   input clk, rst;

   input padv_fetch_i;
   // calculated address from ALU
   input [OPTION_OPERAND_WIDTH-1:0] alu_result_i;

   // register file B in (store operand)
   input [OPTION_OPERAND_WIDTH-1:0] rfb_i;
   // insn opcode, indicating what's going on
   input [`OR1K_OPCODE_WIDTH-1:0]   opc_insn_i;
   // from decode stage regs, indicate if load or store
   input 			    op_lsu_load_i;
   input 			    op_lsu_store_i;

   input 			    exception_taken_i;
   input 			    du_restart_i;
   input 			    stepping_i;
   input 			    next_fetch_done_i;
   

   output [OPTION_OPERAND_WIDTH-1:0] lsu_result_o;
   output 			     lsu_valid_o;
   // exception output
   output 			     lsu_except_dbus_o;
   output 			     lsu_except_align_o;
   
   // interface to data bus
   output [OPTION_OPERAND_WIDTH-1:0] dbus_adr_o;
   output 			     dbus_req_o;
   output [OPTION_OPERAND_WIDTH-1:0] dbus_dat_o;
   output [3:0] 		     dbus_bsel_o;
   output 			     dbus_we_o;
   input 			     dbus_err_i;
   input 			     dbus_ack_i;
   input [OPTION_OPERAND_WIDTH-1:0]  dbus_dat_i;

   reg [OPTION_OPERAND_WIDTH-1:0]    dbus_dat_aligned;  // comb.
   reg [OPTION_OPERAND_WIDTH-1:0]    dbus_dat_extended; // comb.


   reg [OPTION_OPERAND_WIDTH-1:0]    dbus_adr_r;

   reg [3:0] 			     dbus_bsel;
   
   reg 				     access_done;

   reg [OPTION_OPERAND_WIDTH-1:0]    lsu_result_r;
   
   wire 			     align_err_word;
   wire 			     align_err_short;

   wire 			     load_align_err;
   wire 			     store_align_err;

   wire 			     load_sext = !opc_insn_i[0];
   wire 			     load_zext = opc_insn_i[0];


   wire 			     except_align;
   reg 				     except_align_r;

   reg 				     except_dbus;
   reg 				     execute_go;
   wire 			     lsu_go;

   assign dbus_adr_o = execute_go ? alu_result_i : dbus_adr_r;
   assign dbus_dat_o = (opc_insn_i[1:0]==2'b10) ?        // l.sb
		       {rfb_i[7:0],rfb_i[7:0],rfb_i[7:0],rfb_i[7:0]} :
		       (opc_insn_i[1:0]==2'b11) ?        // l.sh
		       {rfb_i[15:0],rfb_i[15:0]} :
		       rfb_i;                         // l.sw
   
   assign dbus_req_o = (op_lsu_load_i | op_lsu_store_i) &
		       !except_align & !access_done;
   
   assign align_err_word = |dbus_adr_o[1:0];
   assign align_err_short = dbus_adr_o[0];
   

   assign lsu_valid_o = dbus_ack_i | dbus_err_i | access_done;
   assign lsu_except_dbus_o = dbus_err_i | except_dbus;

   assign load_align_err = ((opc_insn_i==`OR1K_OPCODE_LWZ |
			     opc_insn_i==`OR1K_OPCODE_LWS) & align_err_word) |
			   ((opc_insn_i==`OR1K_OPCODE_LHZ |
			     opc_insn_i==`OR1K_OPCODE_LHS) & align_err_short);
   
   assign store_align_err = (opc_insn_i==`OR1K_OPCODE_SW & align_err_word) |
			    (opc_insn_i==`OR1K_OPCODE_SH & align_err_short);

   assign except_align = (op_lsu_load_i & load_align_err) |
			 (op_lsu_store_i & store_align_err) ;

   assign lsu_except_align_o = except_align_r;

   assign lsu_go = execute_go & (op_lsu_load_i | op_lsu_store_i);
      
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       execute_go <= 0;
     else
       execute_go <= padv_fetch_i | (stepping_i & next_fetch_done_i);
   
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       access_done <= 0;
     else if (padv_fetch_i | du_restart_i)
       access_done <= 0;
     else if (dbus_ack_i | dbus_err_i | lsu_except_align_o)
       access_done <= 1;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       except_align_r <= 0;
     else if (exception_taken_i)
       except_align_r <= 0;
     else
       except_align_r <= except_align;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       except_dbus <= 0;
     else if (exception_taken_i)
       except_dbus <= 0;
     else if (dbus_err_i)
       except_dbus <= 1;

   // Need to register address due to behavior of RF when source register is
   // same as destination register - value changes after one cycle to the
   // forwarding register's value, which is incorrect.
   // So we save it on first cycle.
   // TODO - perhaps detect in RF when this is case, and make it keep the
   // output steady to avoid an extra address registering stage here.
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       dbus_adr_r <= 0;
     else if (execute_go & (op_lsu_load_i | op_lsu_store_i))
       dbus_adr_r <= alu_result_i;
   
   // Big endian bus mapping
   always @*
     if (op_lsu_load_i) begin
	case(opc_insn_i[2:0])
	  3'b101,
	  3'b110: // load halfword
	    case(dbus_adr_o[1])
	      1'b0:
		dbus_bsel = 4'b1100;
	      1'b1:
		dbus_bsel = 4'b0011;
	    endcase // case (dbus_adr_o[1])
	  3'b011,
	      3'b100: // load byte
		case(dbus_adr_o[1:0])
		  2'b00:
		    dbus_bsel = 4'b1000;
		  2'b01:
		    dbus_bsel = 4'b0100;
		  2'b10:
		    dbus_bsel = 4'b0010;
		  2'b11:
		    dbus_bsel = 4'b0001;
		endcase // case (dbus_adr_o[1:0])
	  default:
	    dbus_bsel = 4'b1111;
	endcase // case (opc_insn_i[1:0])
     end
     else if (op_lsu_store_i) begin
	case(opc_insn_i[1:0])
	  2'b11: // Store halfword
	    case(dbus_adr_o[1])
	      1'b0:
		dbus_bsel = 4'b1100;
	      1'b1:
		dbus_bsel = 4'b0011;
	    endcase // case (dbus_adr_o[1])
	  2'b10: // Store byte
	    case(dbus_adr_o[1:0])
	      2'b00:
		dbus_bsel = 4'b1000;
	      2'b01:
		dbus_bsel = 4'b0100;
	      2'b10:
		dbus_bsel = 4'b0010;
	      2'b11:
		dbus_bsel = 4'b0001;
	    endcase // case (dbus_adr_o[1:0])
	  default:
	    dbus_bsel = 4'b1111;
	endcase // case (opc_insn_i[1:0])
     end // if (op_lsu_store_i)
     else
       dbus_bsel = 4'b0000;

   assign dbus_bsel_o = dbus_bsel;   
   
   assign dbus_we_o =  op_lsu_store_i;

   // Select part of read word
   // Can use registered address here, as it'll take at least one cycle for
   // the data to come back, and by that time dbus_adr_r has the address
   always @*
     case(dbus_adr_r[1:0])
       2'b00:
	 dbus_dat_aligned = dbus_dat_i;
       2'b01:
	 dbus_dat_aligned = {dbus_dat_i[23:0],8'd0};
       2'b10:
	 dbus_dat_aligned = {dbus_dat_i[15:0],16'd0};
       2'b11:
	 dbus_dat_aligned = {dbus_dat_i[7:0],24'd0};
     endcase // case (dbus_adr_r[1:0])
   
   // Do appropriate extension
   always @*
     case(opc_insn_i[0])// zero or sign-extended
       1'b1: // zero extended
	 case(opc_insn_i[2:1])
	   2'b01: // lbz
	     dbus_dat_extended = {24'd0,dbus_dat_aligned[31:24]};
	   2'b10: // lhz
	     dbus_dat_extended = {16'd0,dbus_dat_aligned[31:16]};
	   default:
	     dbus_dat_extended = dbus_dat_aligned;
	 endcase // case (opc_insn_i[2:1])
       1'b0: // sign extended
	 case(opc_insn_i[2:1])
	   2'b10: // lbs
	     dbus_dat_extended = {{24{dbus_dat_aligned[31]}},
				  dbus_dat_aligned[31:24]};
	   2'b11: // lhz
	     dbus_dat_extended = {{16{dbus_dat_aligned[31]}},
				  dbus_dat_aligned[31:16]};
	   default:
	     dbus_dat_extended = dbus_dat_aligned;
	 endcase // case (opc_insn_i[2:1])
     endcase // case (opc_insn_i[0])

   // Register result incase writeback doesn't occur for a few cycles
   // TODO - remove this - we should write straight into the RF!
   always @(posedge clk)
     if (dbus_ack_i & op_lsu_load_i)
       lsu_result_r <= dbus_dat_extended;
   
   assign lsu_result_o = access_done ? lsu_result_r : dbus_dat_extended;

endmodule // mor1kx_lsu
