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
    output 			      dbus_burst_o,
    input 			      dbus_err_i,
    input 			      dbus_ack_i,
    input [OPTION_OPERAND_WIDTH-1:0]  dbus_dat_i,
    input 			      pipeline_flush_i,
    input 			      du_stall_i
    );

   reg [OPTION_OPERAND_WIDTH-1:0]    dbus_dat_aligned;  // comb.
   reg [OPTION_OPERAND_WIDTH-1:0]    dbus_dat_extended; // comb.

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

   wire 			     dbus_ack;
   wire 			     dbus_err;
   wire [OPTION_OPERAND_WIDTH-1:0]   dbus_ldat;
   wire [OPTION_OPERAND_WIDTH-1:0]   dbus_sdat;
   wire [OPTION_OPERAND_WIDTH-1:0]   dbus_adr;
   wire 			     dbus_req;
   reg [3:0] 			     dbus_bsel;
   wire 			     dbus_we;

   wire 			     dc_err;
   wire 			     dc_ack;
   wire [31:0] 			     dc_ldat;
   wire [31:0] 			     dc_sdat;
   wire [OPTION_OPERAND_WIDTH-1:0]   dc_dbus_adr;
   wire 			     dc_dbus_req;
   wire [3:0]			     dc_dbus_bsel;
   wire 			     dc_dbus_we;
   wire [OPTION_OPERAND_WIDTH-1:0]   dc_dbus_sdat;
   wire [31:0] 			     dc_adr;
   wire [31:0] 			     dc_adr_match;
   wire 			     dc_req;
   wire 			     dc_we;
   wire [3:0] 			     dc_bsel;
   wire 			     dc_cache_inhibit;

   wire 			     dc_access;
   wire 			     dc_refill;
   wire 			     dc_refill_done;

   reg 				     dc_enable_r;
   wire 			     dc_enabled;

   // DMMU
   wire 			     tlb_miss;
   wire 			     pagefault;
   wire [OPTION_OPERAND_WIDTH-1:0]   dmmu_phys_addr;
   wire				     except_dtlb_miss;
   reg 				     except_dtlb_miss_r;
   wire 			     except_dpagefault;
   reg 				     except_dpagefault_r;
   wire 			     dmmu_cache_inhibit;

   assign dbus_sdat = (ctrl_opc_insn_i[1:0]==2'b10) ?        // l.sb
		      {ctrl_rfb_i[7:0],ctrl_rfb_i[7:0],ctrl_rfb_i[7:0],ctrl_rfb_i[7:0]} :
		      (ctrl_opc_insn_i[1:0]==2'b11) ?        // l.sh
		      {ctrl_rfb_i[15:0],ctrl_rfb_i[15:0]} :
		      ctrl_rfb_i;                         // l.sw

   assign align_err_word = |ctrl_lsu_adr_i[1:0];
   assign align_err_short = ctrl_lsu_adr_i[0];


   assign lsu_valid_o = dbus_ack | access_done;
   assign lsu_except_dbus_o = dbus_err | except_dbus;

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
     else if (dbus_ack)
       access_done <= 1;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       except_dbus <= 0;
     else if (padv_execute_i | pipeline_flush_i)
       except_dbus <= 0;
     else if (dbus_err)
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
	    case(ctrl_lsu_adr_i[1])
	      1'b0:
		dbus_bsel = 4'b1100;
	      1'b1:
		dbus_bsel = 4'b0011;
	    endcase // case (ctrl_lsu_adr_i[1])
	  3'b011,
	      3'b100: // load byte
		case(ctrl_lsu_adr_i[1:0])
		  2'b00:
		    dbus_bsel = 4'b1000;
		  2'b01:
		    dbus_bsel = 4'b0100;
		  2'b10:
		    dbus_bsel = 4'b0010;
		  2'b11:
		    dbus_bsel = 4'b0001;
		endcase // case (ctrl_lsu_adr_i[1:0])
	  default:
	    dbus_bsel = 4'b1111;
	endcase // case (opc_insn_i[1:0])
     end
     else if (ctrl_op_lsu_store_i) begin
	case(ctrl_opc_insn_i[1:0])
	  2'b11: // Store halfword
	    case(ctrl_lsu_adr_i[1])
	      1'b0:
		dbus_bsel = 4'b1100;
	      1'b1:
		dbus_bsel = 4'b0011;
	    endcase // case (ctrl_lsu_adr_i[1])
	  2'b10: // Store byte
	    case(ctrl_lsu_adr_i[1:0])
	      2'b00:
		dbus_bsel = 4'b1000;
	      2'b01:
		dbus_bsel = 4'b0100;
	      2'b10:
		dbus_bsel = 4'b0010;
	      2'b11:
		dbus_bsel = 4'b0001;
	    endcase // case (ctrl_lsu_adr_i[1:0])
	  default:
	    dbus_bsel = 4'b1111;
	endcase // case (ctrl_opc_insn_i[1:0])
     end // if (ctrl_op_lsu_store_i)
     else
       dbus_bsel = 4'b0000;

   // Select part of read word
   always @*
     case(ctrl_lsu_adr_i[1:0])
       2'b00:
	 dbus_dat_aligned = dbus_ldat;
       2'b01:
	 dbus_dat_aligned = {dbus_ldat[23:0],8'd0};
       2'b10:
	 dbus_dat_aligned = {dbus_ldat[15:0],16'd0};
       2'b11:
	 dbus_dat_aligned = {dbus_ldat[7:0],24'd0};
     endcase // case (ctrl_lsu_adr_i[1:0])

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
     if (dbus_ack & ctrl_op_lsu_load_i)
       lsu_result_r <= dbus_dat_extended;

   assign lsu_result_o = access_done ? lsu_result_r : dbus_dat_extended;

   assign dbus_req = (ctrl_op_lsu_load_i | ctrl_op_lsu_store_i) &
		     !except_align & !(except_dtlb_miss | except_dtlb_miss_r) &
		     !(except_dpagefault | except_dpagefault_r) &
		     !access_done & !(pipeline_flush_i & !du_stall_i);
   assign dbus_we = ctrl_op_lsu_store_i;
   assign dbus_adr = dmmu_enable_i ? dmmu_phys_addr : ctrl_lsu_adr_i;

   wire dbus_access = !dc_access & !dc_refill;
   assign dbus_ack = dbus_access ? dbus_ack_i : dc_ack;
   assign dbus_err = dbus_access ? dbus_err_i : dc_err;
   assign dbus_ldat = dbus_access ? dbus_dat_i : dc_ldat;
   assign dbus_adr_o = dbus_access ? dbus_adr : dc_dbus_adr;
   assign dbus_req_o = dbus_access ? dbus_req : dc_dbus_req;
   assign dbus_we_o = dbus_access ? dbus_we : dc_dbus_we;
   assign dbus_bsel_o = dbus_access ? dbus_bsel : dc_dbus_bsel;
   assign dbus_dat_o = dbus_access ? dbus_sdat : dc_dbus_sdat;
   assign dbus_burst_o = dc_refill & !dc_refill_done;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       dc_enable_r <= 0;
     else if (dc_enable_i & !dbus_req)
       dc_enable_r <= 1;
     else if (!dc_enable_i & !dc_refill)
       dc_enable_r <= 0;

   assign dc_enabled = dc_enable_i & dc_enable_r;
   assign dc_adr = padv_execute_i &
		   (exec_op_lsu_load_i | exec_op_lsu_store_i) ?
		   exec_lsu_adr_i : ctrl_lsu_adr_i;
   assign dc_adr_match = dbus_adr;
   assign dc_req = dbus_req & dc_access;
   assign dc_sdat = dbus_sdat;

generate
if (FEATURE_DATACACHE!="NONE") begin : dcache_gen
   if (OPTION_DCACHE_LIMIT_WIDTH == OPTION_OPERAND_WIDTH) begin
      assign dc_access = dc_enabled &
			 !(dmmu_cache_inhibit & dmmu_enable_i);
   end else if (OPTION_DCACHE_LIMIT_WIDTH < OPTION_OPERAND_WIDTH) begin
      assign dc_access = dc_enabled &
			 dc_adr_match[OPTION_OPERAND_WIDTH-1:
				      OPTION_DCACHE_LIMIT_WIDTH] == 0 &
			 !(dmmu_cache_inhibit & dmmu_enable_i);
   end else begin
      initial begin
	 $display("ERROR: OPTION_DCACHE_LIMIT_WIDTH > OPTION_OPERAND_WIDTH");
	 $finish();
      end
   end

   assign dc_bsel = dbus_bsel;
   assign dc_we = exec_op_lsu_store_i & padv_execute_i;

   /* mor1kx_dcache AUTO_TEMPLATE (
	    .refill_o			(dc_refill),
	    .refill_done_o		(dc_refill_done),
	    .cpu_err_o			(dc_err),
	    .cpu_ack_o			(dc_ack),
	    .cpu_dat_o			(dc_ldat),
	    .dbus_adr_o			(dc_dbus_adr),
	    .dbus_req_o			(dc_dbus_req),
	    .dbus_we_o			(dc_dbus_we),
	    .dbus_bsel_o		(dc_dbus_bsel),
	    .dbus_dat_o			(dc_dbus_sdat),
	    .spr_bus_dat_o		(spr_bus_dat_dc_o),
	    .spr_bus_ack_o		(spr_bus_ack_dc_o),
	    // Inputs
	    .clk			(clk),
	    .rst			(rst),
	    .dc_enable_i		(dc_enabled),
	    .dc_access_i		(dc_access),
	    .cpu_dat_i			(dc_sdat),
	    .cpu_adr_i			(dc_adr),
	    .cpu_adr_match_i		(dc_adr_match),
	    .cpu_req_i			(dc_req),
	    .cpu_we_i			(dc_we),
	    .cpu_bsel_i			(dc_bsel),
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
	    .refill_o			(dc_refill),		 // Templated
	    .refill_done_o		(dc_refill_done),	 // Templated
	    .cpu_err_o			(dc_err),		 // Templated
	    .cpu_ack_o			(dc_ack),		 // Templated
	    .cpu_dat_o			(dc_ldat),		 // Templated
	    .dbus_dat_o			(dc_dbus_sdat),		 // Templated
	    .dbus_adr_o			(dc_dbus_adr),		 // Templated
	    .dbus_req_o			(dc_dbus_req),		 // Templated
	    .dbus_we_o			(dc_dbus_we),		 // Templated
	    .dbus_bsel_o		(dc_dbus_bsel),		 // Templated
	    .spr_bus_dat_o		(spr_bus_dat_dc_o),	 // Templated
	    .spr_bus_ack_o		(spr_bus_ack_dc_o),	 // Templated
	    // Inputs
	    .clk			(clk),			 // Templated
	    .rst			(rst),			 // Templated
	    .dc_enable_i		(dc_enabled),		 // Templated
	    .dc_access_i		(dc_access),		 // Templated
	    .cpu_dat_i			(dc_sdat),		 // Templated
	    .cpu_adr_i			(dc_adr),		 // Templated
	    .cpu_adr_match_i		(dc_adr_match),		 // Templated
	    .cpu_req_i			(dc_req),		 // Templated
	    .cpu_we_i			(dc_we),		 // Templated
	    .cpu_bsel_i			(dc_bsel),		 // Templated
	    .dbus_err_i			(dbus_err_i),
	    .dbus_ack_i			(dbus_ack_i),
	    .dbus_dat_i			(dbus_dat_i[31:0]),
	    .spr_bus_addr_i		(spr_bus_addr_i[15:0]),
	    .spr_bus_we_i		(spr_bus_we_i),
	    .spr_bus_stb_i		(spr_bus_stb_i),
	    .spr_bus_dat_i		(spr_bus_dat_i[OPTION_OPERAND_WIDTH-1:0]));
end else begin
   assign dc_access = 0;
   assign dc_refill = 0;
   assign dc_refill_done = 0;
   assign dc_err = 0;
   assign dc_ack = 0;
   assign dc_sdat = 0;
   assign dc_bsel = 0;
   assign dc_we = 0;
end

endgenerate

generate
if (FEATURE_DMMU!="NONE") begin : dmmu_gen
   wire  [OPTION_OPERAND_WIDTH-1:0] virt_addr;
   wire 			    dmmu_spr_bus_stb;

   assign virt_addr = dc_adr;

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
