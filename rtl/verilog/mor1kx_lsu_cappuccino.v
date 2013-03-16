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
    parameter OPTION_DCACHE_LIMIT_WIDTH = 32,
    parameter FEATURE_DMMU = "NONE",
    parameter OPTION_DMMU_SET_WIDTH = 6,
    parameter OPTION_DMMU_WAYS = 1
    )
   (
    input 			      clk,
    input 			      rst,

    input 			      padv_execute_i,
    input 			      padv_ctrl_i, // needed for dmmu spr
    input 			      decode_valid_i,
    // calculated address from ALU
    input [OPTION_OPERAND_WIDTH-1:0]  exec_lsu_adr_i,
    input [OPTION_OPERAND_WIDTH-1:0]  ctrl_lsu_adr_i,

    // register file B in (store operand)
    input [OPTION_OPERAND_WIDTH-1:0]  ctrl_rfb_i,
    // insn opcode, indicating what's going on
    input [`OR1K_OPCODE_WIDTH-1:0]    ctrl_opc_insn_i,
    // from decode stage regs, indicate if load or store
    input 			      exec_op_lsu_load_i,
    input 			      exec_op_lsu_store_i,
    input 			      ctrl_op_lsu_load_i,
    input 			      ctrl_op_lsu_store_i,

    output [OPTION_OPERAND_WIDTH-1:0] lsu_result_o,
    output 			      lsu_valid_o,
    // exception output
    output 			      lsu_except_dbus_o,
    output 			      lsu_except_align_o,
    output 			      lsu_except_dtlb_miss_o,
    output 			      lsu_except_dpagefault_o,

    // SPR interface
    input [15:0] 		      spr_bus_addr_i,
    input 			      spr_bus_we_i,
    input 			      spr_bus_stb_i,
    input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_i,
    output [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_dc_o,
    output 			      spr_bus_ack_dc_o,
    output [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_dmmu_o,
    output 			      spr_bus_ack_dmmu_o,

    input 			      dc_enable_i,
    input 			      dmmu_enable_i,
    input 			      supervisor_mode_i,

    // interface to data bus
    output [OPTION_OPERAND_WIDTH-1:0] dbus_adr_o,
    output 			      dbus_req_o,
    output [OPTION_OPERAND_WIDTH-1:0] dbus_dat_o,
    output [3:0] 		      dbus_bsel_o,
    output 			      dbus_we_o,
    input 			      dbus_err_i,
    input 			      dbus_ack_i,
    input [OPTION_OPERAND_WIDTH-1:0]  dbus_dat_i,
    input 			      pipeline_flush_i,
    input 			      du_stall_i
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

   wire 			     load_sext = !ctrl_opc_insn_i[0];
   wire 			     load_zext = ctrl_opc_insn_i[0];


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
   wire 			     dc_cache_inhibit;

   // DMMU
   wire 			     tlb_miss;
   wire 			     pagefault;
   wire [OPTION_OPERAND_WIDTH-1:0]   dmmu_phys_addr;
   wire				     except_dtlb_miss;
   reg 				     except_dtlb_miss_r;
   wire 			     except_dpagefault;
   reg 				     except_dpagefault_r;
   wire 			     dmmu_cache_inhibit;

   assign dc_adr_i = dmmu_enable_i ? dmmu_phys_addr : ctrl_lsu_adr_i;
   assign dc_dat_i = (ctrl_opc_insn_i[1:0]==2'b10) ?        // l.sb
		     {ctrl_rfb_i[7:0],ctrl_rfb_i[7:0],ctrl_rfb_i[7:0],ctrl_rfb_i[7:0]} :
		     (ctrl_opc_insn_i[1:0]==2'b11) ?        // l.sh
		     {ctrl_rfb_i[15:0],ctrl_rfb_i[15:0]} :
		     ctrl_rfb_i;                         // l.sw

   assign dc_req_i = (ctrl_op_lsu_load_i | ctrl_op_lsu_store_i) &
		     !except_align & !(except_dtlb_miss | except_dtlb_miss_r) &
		     !(except_dpagefault | except_dpagefault_r) &
		     !access_done & !(pipeline_flush_i & !du_stall_i);

   assign align_err_word = |dc_adr_i[1:0];
   assign align_err_short = dc_adr_i[0];


   assign lsu_valid_o = dc_ack_o | access_done;
   assign lsu_except_dbus_o = dc_err_o | except_dbus;

   assign load_align_err = ((ctrl_opc_insn_i==`OR1K_OPCODE_LWZ |
			     ctrl_opc_insn_i==`OR1K_OPCODE_LWS) &
			    align_err_word) |
			   ((ctrl_opc_insn_i==`OR1K_OPCODE_LHZ |
			     ctrl_opc_insn_i==`OR1K_OPCODE_LHS) &
			    align_err_short);

   assign store_align_err = (ctrl_opc_insn_i==`OR1K_OPCODE_SW & align_err_word) |
			    (ctrl_opc_insn_i==`OR1K_OPCODE_SH & align_err_short);

   assign except_align = (ctrl_op_lsu_load_i & load_align_err) |
			 (ctrl_op_lsu_store_i & store_align_err) ;

   assign lsu_except_align_o = except_align;

   assign except_dtlb_miss = (ctrl_op_lsu_load_i | ctrl_op_lsu_store_i) &
			     tlb_miss & dmmu_enable_i;

   assign lsu_except_dtlb_miss_o = except_dtlb_miss;

   assign except_dpagefault = (ctrl_op_lsu_load_i | ctrl_op_lsu_store_i) &
			      pagefault & dmmu_enable_i;

   assign lsu_except_dpagefault_o = except_dpagefault;


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

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       except_dtlb_miss_r <= 0;
     else if (padv_execute_i)
       except_dtlb_miss_r <= 0;
     else if (except_dtlb_miss)
       except_dtlb_miss_r <= 1;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       except_dpagefault_r <= 0;
     else if (padv_execute_i)
       except_dpagefault_r <= 0;
     else if (except_dpagefault)
       except_dpagefault_r <= 1;

   // Big endian bus mapping
   always @*
     if (ctrl_op_lsu_load_i) begin
	case(ctrl_opc_insn_i[2:0])
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
     else if (ctrl_op_lsu_store_i) begin
	case(ctrl_opc_insn_i[1:0])
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
	endcase // case (ctrl_opc_insn_i[1:0])
     end // if (ctrl_op_lsu_store_i)
     else
       dbus_bsel = 4'b0000;

   assign dc_bsel_i = dbus_bsel;

   assign dc_we_i = ctrl_op_lsu_store_i;

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
     case(ctrl_opc_insn_i[0])// zero or sign-extended
       1'b1: // zero extended
	 case(ctrl_opc_insn_i[2:1])
	   2'b01: // lbz
	     dbus_dat_extended = {24'd0,dbus_dat_aligned[31:24]};
	   2'b10: // lhz
	     dbus_dat_extended = {16'd0,dbus_dat_aligned[31:16]};
	   default:
	     dbus_dat_extended = dbus_dat_aligned;
	 endcase // case (opc_insn_i[2:1])
       1'b0: // sign extended
	 case(ctrl_opc_insn_i[2:1])
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
     if (dc_ack_o & ctrl_op_lsu_load_i)
       lsu_result_r <= dbus_dat_extended;

   assign lsu_result_o = access_done ? lsu_result_r : dbus_dat_extended;

   assign dc_cache_inhibit = dmmu_enable_i & dmmu_cache_inhibit;
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
	    .spr_bus_dat_o		(spr_bus_dat_dc_o),
	    .spr_bus_ack_o		(spr_bus_ack_dc_o),
	    // Inputs
	    .clk			(clk),
	    .rst			(rst),
	    .dc_enable			(dc_enable_i),
	    .cache_inhibit_i		(dc_cache_inhibit),
	    .cpu_dat_i			(dc_dat_i),
	    .cpu_adr_i			(dc_adr_i),
	    .cpu_req_i			(dc_req_i),
	    .cpu_we_i			(dc_we_i),
	    .cpu_bsel_i			(dc_bsel_i),
	    .dc_err_i			(dbus_err_i),
	    .dc_ack_i			(dbus_ack_i),
	    .dc_dat_i			(dbus_dat_i),
    );*/

   mor1kx_dcache
     #(
       .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH),
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
	    .spr_bus_dat_o		(spr_bus_dat_dc_o),	 // Templated
	    .spr_bus_ack_o		(spr_bus_ack_dc_o),	 // Templated
	    // Inputs
	    .clk			(clk),			 // Templated
	    .rst			(rst),			 // Templated
	    .dc_enable			(dc_enable_i),		 // Templated
	    .cache_inhibit_i		(dc_cache_inhibit),	 // Templated
	    .cpu_dat_i			(dc_dat_i),		 // Templated
	    .cpu_adr_i			(dc_adr_i),		 // Templated
	    .cpu_req_i			(dc_req_i),		 // Templated
	    .cpu_we_i			(dc_we_i),		 // Templated
	    .cpu_bsel_i			(dc_bsel_i),		 // Templated
	    .dc_err_i			(dbus_err_i),		 // Templated
	    .dc_ack_i			(dbus_ack_i),		 // Templated
	    .dc_dat_i			(dbus_dat_i),		 // Templated
	    .spr_bus_addr_i		(spr_bus_addr_i[15:0]),
	    .spr_bus_we_i		(spr_bus_we_i),
	    .spr_bus_stb_i		(spr_bus_stb_i),
	    .spr_bus_dat_i		(spr_bus_dat_i[OPTION_OPERAND_WIDTH-1:0]));
end else begin
   assign dc_err_o = dbus_err_i;
   assign dc_ack_o = dbus_ack_i;
   assign dc_dat_o = dbus_dat_i;
   assign dbus_dat_o = dc_dat_i;
   assign dbus_adr_o = dc_adr_i;
   assign dbus_we_o = dc_we_i;
   assign dbus_bsel_o = dc_bsel_i;
   assign dbus_req_o = dc_req_i;
end

endgenerate

generate
if (FEATURE_DMMU!="NONE") begin : dmmu_gen
   wire  [OPTION_OPERAND_WIDTH-1:0] virt_addr;
   wire 			    dmmu_spr_bus_stb;

   assign virt_addr = padv_execute_i &
		      (exec_op_lsu_load_i | exec_op_lsu_store_i) ?
		      exec_lsu_adr_i : ctrl_lsu_adr_i;

   // small hack to delay dmmu spr reads by one cycle
   // ideally the spr accesses should work so that the address is presented
   // in execute stage and the delayed data should be available in control
   // stage, but this is not how things currently work.
   assign dmmu_spr_bus_stb = spr_bus_stb_i & (!padv_ctrl_i | spr_bus_we_i);

   /* mor1kx_dmmu AUTO_TEMPLATE (
    .phys_addr_o		(dmmu_phys_addr),
    .cache_inhibit_o		(dmmu_cache_inhibit),
    .op_store_i			(ctrl_op_lsu_store_i),
    .op_load_i			(ctrl_op_lsu_load_i),
    .tlb_miss_o			(tlb_miss),
    .pagefault_o		(pagefault),
    .spr_bus_dat_o		(spr_bus_dat_dmmu_o),
    .spr_bus_ack_o		(spr_bus_ack_dmmu_o),
    .spr_bus_stb_i		(dmmu_spr_bus_stb),
    .virt_addr_i		(virt_addr),
    .virt_addr_match_i		(ctrl_lsu_adr_i),
    ); */
   mor1kx_dmmu
     #(
       .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH),
       .OPTION_DMMU_SET_WIDTH(OPTION_DMMU_SET_WIDTH),
       .OPTION_DMMU_WAYS(OPTION_DMMU_WAYS)
       )
   mor1kx_dmmu
     (/*AUTOINST*/
      // Outputs
      .phys_addr_o			(dmmu_phys_addr),	 // Templated
      .cache_inhibit_o			(dmmu_cache_inhibit),	 // Templated
      .tlb_miss_o			(tlb_miss),		 // Templated
      .pagefault_o			(pagefault),		 // Templated
      .spr_bus_dat_o			(spr_bus_dat_dmmu_o),	 // Templated
      .spr_bus_ack_o			(spr_bus_ack_dmmu_o),	 // Templated
      // Inputs
      .clk				(clk),
      .rst				(rst),
      .virt_addr_i			(virt_addr),		 // Templated
      .virt_addr_match_i		(ctrl_lsu_adr_i),	 // Templated
      .op_store_i			(ctrl_op_lsu_store_i),	 // Templated
      .op_load_i			(ctrl_op_lsu_load_i),	 // Templated
      .supervisor_mode_i		(supervisor_mode_i),
      .spr_bus_addr_i			(spr_bus_addr_i[15:0]),
      .spr_bus_we_i			(spr_bus_we_i),
      .spr_bus_stb_i			(dmmu_spr_bus_stb),	 // Templated
      .spr_bus_dat_i			(spr_bus_dat_i[OPTION_OPERAND_WIDTH-1:0]));
end else begin
   assign dmmu_cache_inhibit = 0;
end
endgenerate

endmodule // mor1kx_lsu_cappuccino
