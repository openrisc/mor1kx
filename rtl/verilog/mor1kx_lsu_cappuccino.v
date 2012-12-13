/* ****************************************************************************
  This Source Code Form is subject to the terms of the
  Open Hardware Description License, v. 1.0. If a copy
  of the OHDL was not distributed with this file, You
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description:  Data bus interface

  All combinatorial outputs to pipeline
  Dbus interface request signal out synchronous

  32-bit specific

  TODO: posted accesses - if we're not currently doing another posted access
  then immediately signal valid to not hold up the pipeline and in the case of
  loads remember the register we were supposed to access, and monitor the
  pipeline for a read from that register, and then indicate we're waiting for
  the read to come through before we can continue

  Copyright (C) 2012 Authors

  Author(s): Julius Baxter <juliusbaxter@gmail.com>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_lsu_cappuccino
  #(
    parameter FEATURE_DATACACHE	= "NONE",
    parameter OPTION_OPERAND_WIDTH = 32,
    parameter OPTION_DCACHE_BLOCK_WIDTH = 5,
    parameter OPTION_DCACHE_SET_WIDTH = 9,
    parameter OPTION_DCACHE_WAYS = 2,
    parameter OPTION_DCACHE_LIMIT_WIDTH = 32
    )
   (
    input 			      clk,
    input 			      rst,

    input 			      padv_execute_i,
    input 			      decode_valid_i,
    // calculated address from ALU
    input [OPTION_OPERAND_WIDTH-1:0]  lsu_adr_i,

    // register file B in (store operand)
    input [OPTION_OPERAND_WIDTH-1:0]  rfb_i,
    // insn opcode, indicating what's going on
    input [`OR1K_OPCODE_WIDTH-1:0]    opc_insn_i,
    // from decode stage regs, indicate if load or store
    input 			      op_lsu_load_i,
    input 			      op_lsu_store_i,

    output [OPTION_OPERAND_WIDTH-1:0] lsu_result_o,
    output 			      lsu_valid_o,
    // exception output
    output 			      lsu_except_dbus_o,
    output 			      lsu_except_align_o,

    // Cache interface
    input [15:0] 		      spr_bus_addr_i,
    input 			      spr_bus_we_i,
    input 			      spr_bus_stb_i,
    input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_i,
    output [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o,
    output 			      spr_bus_ack_o,
    input 			      dc_enable,

    // interface to data bus
    output [OPTION_OPERAND_WIDTH-1:0] dbus_adr_o,
    output 			      dbus_req_o,
    output [OPTION_OPERAND_WIDTH-1:0] dbus_dat_o,
    output [3:0] 		      dbus_bsel_o,
    output 			      dbus_we_o,
    input 			      dbus_err_i,
    input 			      dbus_ack_i,
    input [OPTION_OPERAND_WIDTH-1:0]  dbus_dat_i,
    input 			      pipeline_flush_i
    );

   reg [OPTION_OPERAND_WIDTH-1:0]    dbus_dat_aligned;  // comb.
   reg [OPTION_OPERAND_WIDTH-1:0]    dbus_dat_extended; // comb.

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

   reg 				     except_dbus;

   wire 			     dc_err_o;
   wire 			     dc_ack_o;
   wire [31:0] 			     dc_dat_o;
   wire [31:0] 			     dc_dat_i;
   wire [31:0] 			     dc_adr_i;
   wire 			     dc_req_i;
   wire 			     dc_we_i;
   wire [3:0] 			     dc_bsel_i;

   assign dc_adr_i = lsu_adr_i;
   assign dc_dat_i = (opc_insn_i[1:0]==2'b10) ?        // l.sb
		     {rfb_i[7:0],rfb_i[7:0],rfb_i[7:0],rfb_i[7:0]} :
		     (opc_insn_i[1:0]==2'b11) ?        // l.sh
		     {rfb_i[15:0],rfb_i[15:0]} :
		     rfb_i;                         // l.sw

   assign dc_req_i = (op_lsu_load_i | op_lsu_store_i) &
		     !except_align & !access_done & !pipeline_flush_i;

   assign align_err_word = |dc_adr_i[1:0];
   assign align_err_short = dc_adr_i[0];


   assign lsu_valid_o = dc_ack_o | access_done;
   assign lsu_except_dbus_o = dc_err_o | except_dbus;

   assign load_align_err = ((opc_insn_i==`OR1K_OPCODE_LWZ |
			     opc_insn_i==`OR1K_OPCODE_LWS) & align_err_word) |
			   ((opc_insn_i==`OR1K_OPCODE_LHZ |
			     opc_insn_i==`OR1K_OPCODE_LHS) & align_err_short);

   assign store_align_err = (opc_insn_i==`OR1K_OPCODE_SW & align_err_word) |
			    (opc_insn_i==`OR1K_OPCODE_SH & align_err_short);

   assign except_align = (op_lsu_load_i & load_align_err) |
			 (op_lsu_store_i & store_align_err) ;

   assign lsu_except_align_o = except_align;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       access_done <= 0;
     else if (padv_execute_i)
       access_done <= 0;
     else if (dc_ack_o)
       access_done <= 1;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       except_dbus <= 0;
     else if (padv_execute_i | pipeline_flush_i)
       except_dbus <= 0;
     else if (dc_err_o)
       except_dbus <= 1;

   // Big endian bus mapping
   always @*
     if (op_lsu_load_i) begin
	case(opc_insn_i[2:0])
	  3'b101,
	  3'b110: // load halfword
	    case(dc_adr_i[1])
	      1'b0:
		dbus_bsel = 4'b1100;
	      1'b1:
		dbus_bsel = 4'b0011;
	    endcase // case (dbus_adr_o[1])
	  3'b011,
	      3'b100: // load byte
		case(dc_adr_i[1:0])
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
	    case(dc_adr_i[1])
	      1'b0:
		dbus_bsel = 4'b1100;
	      1'b1:
		dbus_bsel = 4'b0011;
	    endcase // case (dbus_adr_o[1])
	  2'b10: // Store byte
	    case(dc_adr_i[1:0])
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

   assign dc_bsel_i = dbus_bsel;

   assign dc_we_i = op_lsu_store_i;

   // Select part of read word
   always @*
     case(dc_adr_i[1:0])
       2'b00:
	 dbus_dat_aligned = dc_dat_o;
       2'b01:
	 dbus_dat_aligned = {dc_dat_o[23:0],8'd0};
       2'b10:
	 dbus_dat_aligned = {dc_dat_o[15:0],16'd0};
       2'b11:
	 dbus_dat_aligned = {dc_dat_o[7:0],24'd0};
     endcase // case (dc_adr_i[1:0])

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
   always @(posedge clk)
     if (dc_ack_o & op_lsu_load_i)
       lsu_result_r <= dbus_dat_extended;

   assign lsu_result_o = access_done ? lsu_result_r : dbus_dat_extended;

generate
if (FEATURE_DATACACHE!="NONE") begin : dcache_gen

   /* mor1kx_dcache AUTO_TEMPLATE (
	    .cpu_err_o			(dc_err_o),
	    .cpu_ack_o			(dc_ack_o),
	    .cpu_dat_o			(dc_dat_o),
	    .dc_dat_o			(dbus_dat_o),
	    .dc_adr_o			(dbus_adr_o),
	    .dc_req_o			(dbus_req_o),
	    .dc_we_o			(dbus_we_o),
	    .dc_bsel_o			(dbus_bsel_o),
	    .spr_bus_dat_o		(spr_bus_dat_o),
	    .spr_bus_ack_o		(spr_bus_ack_o),
	    // Inputs
	    .clk			(clk),
	    .rst			(rst),
	    .dc_enable			(dc_enable),
	    .cpu_dat_i			(dc_dat_i),
	    .cpu_adr_i			(dc_adr_i),
	    .cpu_req_i			(dc_req_i),
	    .cpu_we_i			(dc_we_i),
	    .cpu_bsel_i			(dc_bsel_i),
	    .dc_err_i			(dbus_err_i),
	    .dc_ack_i			(dbus_ack_i),
	    .dc_dat_i			(dbus_dat_i),
	    .spr_bus_addr_i		(spr_bus_addr_i),
	    .spr_bus_we_i		(spr_bus_we_i),
	    .spr_bus_stb_i		(spr_bus_stb_i),
	    .spr_bus_dat_i		(spr_bus_dat_i),
    );*/

   mor1kx_dcache
     #(
       .OPTION_DCACHE_BLOCK_WIDTH(OPTION_DCACHE_BLOCK_WIDTH),
       .OPTION_DCACHE_SET_WIDTH(OPTION_DCACHE_SET_WIDTH),
       .OPTION_DCACHE_WAYS(OPTION_DCACHE_WAYS),
       .OPTION_DCACHE_LIMIT_WIDTH(OPTION_DCACHE_LIMIT_WIDTH)
       )
   mor1kx_dcache
	   (/*AUTOINST*/
	    // Outputs
	    .cpu_err_o			(dc_err_o),		 // Templated
	    .cpu_ack_o			(dc_ack_o),		 // Templated
	    .cpu_dat_o			(dc_dat_o),		 // Templated
	    .dc_dat_o			(dbus_dat_o),		 // Templated
	    .dc_adr_o			(dbus_adr_o),		 // Templated
	    .dc_req_o			(dbus_req_o),		 // Templated
	    .dc_we_o			(dbus_we_o),		 // Templated
	    .dc_bsel_o			(dbus_bsel_o),		 // Templated
	    .spr_bus_dat_o		(spr_bus_dat_o),	 // Templated
	    .spr_bus_ack_o		(spr_bus_ack_o),	 // Templated
	    // Inputs
	    .clk			(clk),			 // Templated
	    .rst			(rst),			 // Templated
	    .dc_enable			(dc_enable),		 // Templated
	    .cpu_dat_i			(dc_dat_i),		 // Templated
	    .cpu_adr_i			(dc_adr_i),		 // Templated
	    .cpu_req_i			(dc_req_i),		 // Templated
	    .cpu_we_i			(dc_we_i),		 // Templated
	    .cpu_bsel_i			(dc_bsel_i),		 // Templated
	    .dc_err_i			(dbus_err_i),		 // Templated
	    .dc_ack_i			(dbus_ack_i),		 // Templated
	    .dc_dat_i			(dbus_dat_i),		 // Templated
	    .spr_bus_addr_i		(spr_bus_addr_i),	 // Templated
	    .spr_bus_we_i		(spr_bus_we_i),		 // Templated
	    .spr_bus_stb_i		(spr_bus_stb_i),	 // Templated
	    .spr_bus_dat_i		(spr_bus_dat_i));	 // Templated
end else begin
   assign dc_err_o = dbus_err_i;
   assign dc_ack_o = dbus_ack_i;
   assign dc_dat_o = dbus_dat_i;
   assign dbus_dat_o = dc_dat_i;
   assign dbus_adr_o = dc_adr_i;
   assign dbus_we_o = dc_we_i;
   assign dbus_bsel_o = dc_we_i;
   assign dbus_req_o = dc_req_i;
end

endgenerate

endmodule // mor1kx_lsu_cappuccino
