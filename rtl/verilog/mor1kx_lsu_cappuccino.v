/* ****************************************************************************
  SPDX-License-Identifier: CERN-OHL-W-2.0

  Description:  Data bus interface

  All combinatorial outputs to pipeline
  Dbus interface request signal out synchronous

  32-bit specific

  Copyright (C) 2012 Julius Baxter <juliusbaxter@gmail.com>
  Copyright (C) 2013 Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>

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
    parameter OPTION_DCACHE_SNOOP = "NONE",
    parameter FEATURE_DMMU = "NONE",
    parameter FEATURE_DMMU_HW_TLB_RELOAD = "NONE",
    parameter OPTION_DMMU_SET_WIDTH = 6,
    parameter OPTION_DMMU_WAYS = 1,
    parameter FEATURE_STORE_BUFFER = "ENABLED",
    parameter OPTION_STORE_BUFFER_DEPTH_WIDTH = 8,
    parameter FEATURE_ATOMIC = "ENABLED"
    )
   (
    input 			      clk,
    input 			      rst,

    input 			      padv_execute_i,
    input 			      padv_ctrl_i, // needed for dmmu spr
    // calculated address from ALU
    input [OPTION_OPERAND_WIDTH-1:0]  exec_lsu_adr_i,
    input [OPTION_OPERAND_WIDTH-1:0]  ctrl_lsu_adr_i,

    // register file B in (store operand)
    input [OPTION_OPERAND_WIDTH-1:0]  ctrl_rfb_i,

    // from decode stage regs, indicate if load or store
    input 			      exec_op_lsu_load_i,
    input 			      exec_op_lsu_store_i,
    input 			      exec_op_lsu_atomic_i,
    input 			      ctrl_op_lsu_load_i,
    input 			      ctrl_op_lsu_store_i,
    input 			      ctrl_op_lsu_atomic_i,
    input                             ctrl_op_msync_i,
    input [1:0] 		      ctrl_lsu_length_i,
    input 			      ctrl_lsu_zext_i,

    // From control stage, exception PC for the store buffer input
    input [OPTION_OPERAND_WIDTH-1:0]  ctrl_epcr_i,
    // The exception PC as it has went through the store buffer
    output [OPTION_OPERAND_WIDTH-1:0] store_buffer_epcr_o,

    output [OPTION_OPERAND_WIDTH-1:0] lsu_result_o,
    output 			      lsu_valid_o,
    // exception output
    output 			      lsu_except_dbus_o,
    output 			      lsu_except_align_o,
    output 			      lsu_except_dtlb_miss_o,
    output 			      lsu_except_dpagefault_o,

    // Indicator that the dbus exception came via the store buffer
    output reg 			      store_buffer_err_o,

    // Atomic operation flag set/clear logic
    output 			      atomic_flag_set_o,
    output 			      atomic_flag_clear_o,

    // stall signal for msync logic
    output                            msync_stall_o,

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
    output 			      dc_hit_o,

    // interface to data bus
    output [OPTION_OPERAND_WIDTH-1:0] dbus_adr_o,
    output reg			      dbus_req_o,
    output [OPTION_OPERAND_WIDTH-1:0] dbus_dat_o,
    output reg [3:0] 		      dbus_bsel_o,
    output 			      dbus_we_o,
    output 			      dbus_burst_o,
    input 			      dbus_err_i,
    input 			      dbus_ack_i,
    input [OPTION_OPERAND_WIDTH-1:0]  dbus_dat_i,
    input 			      pipeline_flush_i,

    input [31:0] 		      snoop_adr_i,
    input 			      snoop_en_i
    );

   reg [OPTION_OPERAND_WIDTH-1:0]    dbus_dat_aligned;  // comb.
   reg [OPTION_OPERAND_WIDTH-1:0]    dbus_dat_extended; // comb.

   reg 				     access_done;

   wire 			     align_err_word;
   wire 			     align_err_short;

   wire 			     align_err;

   wire 			     except_align;

   reg 				     except_dbus;

   reg 				     dbus_ack;
   reg 				     dbus_err;
   reg [OPTION_OPERAND_WIDTH-1:0]    dbus_dat;
   reg [OPTION_OPERAND_WIDTH-1:0]    dbus_adr;
   wire [OPTION_OPERAND_WIDTH-1:0]   next_dbus_adr;
   reg 				     dbus_we;
   reg [3:0] 			     dbus_bsel;
   wire 			     dbus_access;
   wire 			     dbus_stall;

   wire [OPTION_OPERAND_WIDTH-1:0]   lsu_ldat;
   wire [OPTION_OPERAND_WIDTH-1:0]   lsu_sdat;
   wire				     lsu_ack;

   wire 			     dc_ack;
   wire 			     dc_err;
   wire [31:0] 			     dc_ldat;
   wire [31:0] 			     dc_sdat;
   wire [31:0] 			     dc_adr;
   wire [31:0] 			     dc_adr_match;
   wire 			     dc_we;
   wire [3:0] 			     dc_bsel;

   wire 			     dc_access;
   wire 			     dc_refill_allowed;
   wire 			     dc_refill;
   wire 			     dc_refill_req;
   wire 			     dc_refill_done;

   reg 				     dc_enable_r;
   wire 			     dc_enabled;

   wire 			     ctrl_op_lsu;

   // DMMU
   wire 			     tlb_miss;
   wire 			     pagefault;
   wire [OPTION_OPERAND_WIDTH-1:0]   dmmu_phys_addr;
   wire				     except_dtlb_miss;
   reg 				     except_dtlb_miss_r;
   wire 			     except_dpagefault;
   reg 				     except_dpagefault_r;
   wire 			     dmmu_cache_inhibit;

   wire 			     tlb_reload_req;
   wire 			     tlb_reload_busy;
   wire [OPTION_OPERAND_WIDTH-1:0]   tlb_reload_addr;
   wire 			     tlb_reload_pagefault;
   reg 				     tlb_reload_ack;
   reg [OPTION_OPERAND_WIDTH-1:0]    tlb_reload_data;
   wire				     tlb_reload_pagefault_clear;
   reg 				     tlb_reload_done;

   // Store buffer
   wire 			     store_buffer_write;
   wire				     store_buffer_read;
   wire 			     store_buffer_full;
   wire 			     store_buffer_empty;
   wire [OPTION_OPERAND_WIDTH-1:0]   store_buffer_radr;
   wire [OPTION_OPERAND_WIDTH-1:0]   store_buffer_wadr;
   wire [OPTION_OPERAND_WIDTH-1:0]   store_buffer_dat;
   wire [OPTION_OPERAND_WIDTH/8-1:0] store_buffer_bsel;
   wire 			     store_buffer_atomic;
   reg 				     store_buffer_write_pending;

   reg 				     dbus_atomic;

   reg 				     last_write;
   // write_done indicates the store buffer has been flushed
   reg 				     write_done;

   // Atomic operations
   reg [OPTION_OPERAND_WIDTH-1:0]    atomic_addr;
   reg 				     atomic_reserve;
   wire				     swa_success;

   wire 			     snoop_valid;
   wire 			     dc_snoop_hit;

   // We have to mask out our snooped bus accesses
   assign snoop_valid = (OPTION_DCACHE_SNOOP != "NONE") ?
                        snoop_en_i & !((snoop_adr_i == dbus_adr_o) & dbus_ack_i) :
                        0;

   assign ctrl_op_lsu = ctrl_op_lsu_load_i | ctrl_op_lsu_store_i;

   assign lsu_sdat = (ctrl_lsu_length_i == 2'b00) ? // byte access
		     {ctrl_rfb_i[7:0],ctrl_rfb_i[7:0],
		      ctrl_rfb_i[7:0],ctrl_rfb_i[7:0]} :
		     (ctrl_lsu_length_i == 2'b01) ? // halfword access
		     {ctrl_rfb_i[15:0],ctrl_rfb_i[15:0]} :
		     ctrl_rfb_i;                    // word access

   assign align_err_word = |ctrl_lsu_adr_i[1:0];
   assign align_err_short = ctrl_lsu_adr_i[0];


   assign lsu_valid_o = (lsu_ack | access_done) & !tlb_reload_busy & !dc_snoop_hit;

   assign lsu_except_dbus_o = except_dbus | store_buffer_err_o;

   assign align_err = (ctrl_lsu_length_i == 2'b10) & align_err_word |
		      (ctrl_lsu_length_i == 2'b01) & align_err_short;

   assign except_align = ctrl_op_lsu & align_err;

   assign lsu_except_align_o = except_align & !pipeline_flush_i;

   assign except_dtlb_miss = ctrl_op_lsu & tlb_miss & dmmu_enable_i &
			     !tlb_reload_busy;

   assign lsu_except_dtlb_miss_o = except_dtlb_miss & !pipeline_flush_i;

   assign except_dpagefault = ctrl_op_lsu & pagefault & dmmu_enable_i &
			      !tlb_reload_busy | tlb_reload_pagefault;

   assign lsu_except_dpagefault_o = except_dpagefault & !pipeline_flush_i;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       access_done <= 0;
     else if (padv_execute_i)
       access_done <= 0;
     else if (lsu_ack)
       access_done <= 1;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       except_dbus <= 0;
     else if (padv_execute_i | pipeline_flush_i)
       except_dbus <= 0;
     else if (dbus_err_i)
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

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       store_buffer_err_o <= 0;
     else if (pipeline_flush_i)
       store_buffer_err_o <= 0;
     else if (dbus_err_i & dbus_we_o)
       store_buffer_err_o <= 1;

   // Big endian bus mapping
   always @(*)
     case (ctrl_lsu_length_i)
       2'b00: // byte access
	 case(ctrl_lsu_adr_i[1:0])
	   2'b00:
	     dbus_bsel = 4'b1000;
	   2'b01:
	     dbus_bsel = 4'b0100;
	   2'b10:
	     dbus_bsel = 4'b0010;
	   2'b11:
	     dbus_bsel = 4'b0001;
	 endcase
       2'b01: // halfword access
	    case(ctrl_lsu_adr_i[1])
	      1'b0:
		dbus_bsel = 4'b1100;
	      1'b1:
		dbus_bsel = 4'b0011;
	    endcase
       2'b10,
       2'b11:
	 dbus_bsel = 4'b1111;
     endcase

   // Select part of read word
   always @*
     case(ctrl_lsu_adr_i[1:0])
       2'b00:
	 dbus_dat_aligned = lsu_ldat;
       2'b01:
	 dbus_dat_aligned = {lsu_ldat[23:0],8'd0};
       2'b10:
	 dbus_dat_aligned = {lsu_ldat[15:0],16'd0};
       2'b11:
	 dbus_dat_aligned = {lsu_ldat[7:0],24'd0};
     endcase // case (ctrl_lsu_adr_i[1:0])

   // Do appropriate extension
   always @(*)
     case({ctrl_lsu_zext_i, ctrl_lsu_length_i})
       3'b100: // lbz
	 dbus_dat_extended = {24'd0,dbus_dat_aligned[31:24]};
       3'b101: // lhz
	 dbus_dat_extended = {16'd0,dbus_dat_aligned[31:16]};
       3'b000: // lbs
	 dbus_dat_extended = {{24{dbus_dat_aligned[31]}},
			      dbus_dat_aligned[31:24]};
       3'b001: // lhs
	 dbus_dat_extended = {{16{dbus_dat_aligned[31]}},
			      dbus_dat_aligned[31:16]};
       default:
	 dbus_dat_extended = dbus_dat_aligned;
     endcase

   assign lsu_result_o = dbus_dat_extended;

   // Bus access logic
   localparam [2:0]
     IDLE		= 3'd0,
     READ		= 3'd1,
     WRITE		= 3'd2,
     TLB_RELOAD		= 3'd3,
     DC_REFILL		= 3'd4;

   reg [2:0] state;

   assign dbus_access = (!dc_access | tlb_reload_busy | ctrl_op_lsu_store_i) &
			(state != DC_REFILL) | (state == WRITE);
   reg      dc_refill_r;

   always @(posedge clk)
     dc_refill_r <= dc_refill;

   wire     store_buffer_ack;
   assign store_buffer_ack = (FEATURE_STORE_BUFFER!="NONE") ?
			     store_buffer_write :
			     write_done;
			     
   // If we are writing we wait for the store buffer ack and
   // in case of dcache being busy we wait for data cache ack too
   assign lsu_ack = (ctrl_op_lsu_store_i | state == WRITE) ?
                     (ctrl_op_lsu_atomic_i ? write_done : store_buffer_ack) :
		     (dbus_access ? dbus_ack : dc_ack);

   assign lsu_ldat = dbus_access ? dbus_dat : dc_ldat;
   assign dbus_adr_o = dbus_adr;

   assign dbus_dat_o = dbus_dat;

   assign dbus_burst_o = (state == DC_REFILL) & !dc_refill_done;

   //
   // Slightly subtle, but if there is an atomic store coming out from the
   // store buffer, and the link has been broken while it was waiting there,
   // the bus access is still performed as a (discarded) read.
   //
   assign dbus_we_o = dbus_we & (!dbus_atomic | atomic_reserve);

   assign next_dbus_adr = (OPTION_DCACHE_BLOCK_WIDTH == 5) ?
			  {dbus_adr[31:5], dbus_adr[4:0] + 5'd4} : // 32 byte
			  {dbus_adr[31:4], dbus_adr[3:0] + 4'd4};  // 16 byte

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       dbus_err <= 0;
     else
       dbus_err <= dbus_err_i;

   always @(posedge clk) begin
      dbus_ack <= 0;
      write_done <= 0;
      tlb_reload_ack <= 0;
      tlb_reload_done <= 0;
      case (state)
	IDLE: begin
	   dbus_req_o <= 0;
	   dbus_we <= 0;
	   dbus_adr <= 0;
	   dbus_bsel_o <= 4'hf;
	   dbus_atomic <= 0;
	   last_write <= 0;
	   if (store_buffer_write | !store_buffer_empty) begin
	      state <= WRITE;
	   end else if (ctrl_op_lsu & dbus_access & !dc_refill & !dbus_ack &
			!dbus_err & !except_dbus & !access_done &
			!pipeline_flush_i) begin
	      if (tlb_reload_req) begin
		 dbus_adr <= tlb_reload_addr;
		 dbus_req_o <= 1;
		 state <= TLB_RELOAD;
	      end else if (dmmu_enable_i) begin
		 dbus_adr <= dmmu_phys_addr;
		 if (!tlb_miss & !pagefault & !except_align) begin
		    if (ctrl_op_lsu_load_i) begin
		       dbus_req_o <= 1;
		       dbus_bsel_o <= dbus_bsel;
		       state <= READ;
		    end
		 end
	      end else if (!except_align) begin
		 dbus_adr <= ctrl_lsu_adr_i;
		 if (ctrl_op_lsu_load_i) begin
		    dbus_req_o <= 1;
		    dbus_bsel_o <= dbus_bsel;
		    state <= READ;
		 end
	      end
	   end else if (dc_refill_req) begin
	      dbus_req_o <= 1;
	      dbus_adr <= dc_adr_match;
	      state <= DC_REFILL;
	   end
	end

	DC_REFILL: begin
	   dbus_req_o <= 1;
	   if (dbus_ack_i) begin
	      dbus_adr <= next_dbus_adr;
	      if (dc_refill_done) begin
		 dbus_req_o <= 0;
		 state <= IDLE;
	      end
	   end

	   // TODO: only abort on snoop-hits to refill address
	   if (dbus_err_i | dc_snoop_hit) begin
	      dbus_req_o <= 0;
	      state <= IDLE;
	   end
	end

	READ: begin
	   dbus_ack <= dbus_ack_i;
	   dbus_dat <= dbus_dat_i;
	   if (dbus_ack_i | dbus_err_i) begin
	      dbus_req_o <= 0;
	      state <= IDLE;
	   end
	end

	WRITE: begin
	   dbus_req_o <= 1;
	   dbus_we <= 1;

	   if (!dbus_req_o | dbus_ack_i & !last_write) begin
	      dbus_bsel_o <= store_buffer_bsel;
	      dbus_adr <= store_buffer_radr;
	      dbus_dat <= store_buffer_dat;
	      dbus_atomic <= store_buffer_atomic;
	      last_write <= store_buffer_empty;
	   end

	   if (store_buffer_write)
	     last_write <= 0;

	   if (last_write & dbus_ack_i | dbus_err_i) begin
	      dbus_req_o <= 0;
	      dbus_we <= 0;
	      if (!store_buffer_write) begin
		 state <= IDLE;
		 write_done <= 1;
	      end
	   end
	end

	TLB_RELOAD: begin
	   dbus_adr <= tlb_reload_addr;
	   tlb_reload_data <= dbus_dat_i;
	   tlb_reload_ack <= dbus_ack_i & tlb_reload_req;

	   if (!tlb_reload_req | dbus_err_i) begin
	      state <= IDLE;
	      tlb_reload_done <= 1;
	   end

	   dbus_req_o <= tlb_reload_req;
	   if (dbus_ack_i | tlb_reload_ack)
	     dbus_req_o <= 0;
	end

	default:
	  state <= IDLE;
      endcase

      if (rst)
	state <= IDLE;
   end

   assign dbus_stall = tlb_reload_busy | except_align | except_dbus |
		       except_dtlb_miss | except_dpagefault |
		       pipeline_flush_i;

   // Stall until the store buffer is empty
   assign msync_stall_o = ctrl_op_msync_i & (state == WRITE);

generate
if (FEATURE_ATOMIC!="NONE") begin : atomic_gen
   // Atomic operations logic
   reg atomic_flag_set;
   reg atomic_flag_clear;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       atomic_reserve <= 0;
     else if (pipeline_flush_i)
       atomic_reserve <= 0;
     else if (ctrl_op_lsu_store_i & ctrl_op_lsu_atomic_i & write_done ||
	      !ctrl_op_lsu_atomic_i & store_buffer_write &
	      (store_buffer_wadr == atomic_addr) ||
	      (snoop_valid & (snoop_adr_i == atomic_addr)))
       atomic_reserve <= 0;
     else if (ctrl_op_lsu_load_i & ctrl_op_lsu_atomic_i & padv_ctrl_i)
       atomic_reserve <= !(snoop_valid & (snoop_adr_i == dc_adr_match));

   always @(posedge clk)
     if (ctrl_op_lsu_load_i & ctrl_op_lsu_atomic_i & padv_ctrl_i)
       atomic_addr <= dc_adr_match;

   assign swa_success = ctrl_op_lsu_store_i & ctrl_op_lsu_atomic_i &
			atomic_reserve & (dbus_adr == atomic_addr);

   always @(posedge clk)
     if (padv_ctrl_i)
       atomic_flag_set <= 0;
     else if (write_done)
       atomic_flag_set <= swa_success & lsu_valid_o;

   always @(posedge clk)
     if (padv_ctrl_i)
       atomic_flag_clear <= 0;
     else if (write_done)
       atomic_flag_clear <= !swa_success & lsu_valid_o &
			    ctrl_op_lsu_atomic_i & ctrl_op_lsu_store_i;

   assign atomic_flag_set_o = atomic_flag_set;
   assign atomic_flag_clear_o = atomic_flag_clear;

end else begin
   assign atomic_flag_set_o = 0;
   assign atomic_flag_clear_o = 0;
   assign swa_success = 0;
   always @(posedge clk) begin
      atomic_addr <= 0;
      atomic_reserve <= 0;
   end
end
endgenerate

   // Store buffer logic
   always @(posedge clk)
     if (rst)
       store_buffer_write_pending <= 0;
     else if (store_buffer_write | pipeline_flush_i)
       store_buffer_write_pending <= 0;
     else if (ctrl_op_lsu_store_i & padv_ctrl_i & !dbus_stall &
	      (store_buffer_full | dc_refill | dc_refill_r | dc_snoop_hit))
       store_buffer_write_pending <= 1;

   assign store_buffer_write = (ctrl_op_lsu_store_i &
				(padv_ctrl_i | tlb_reload_done) |
				store_buffer_write_pending) &
			       !store_buffer_full & !dc_refill & !dc_refill_r &
			       !dbus_stall & !dc_snoop_hit;

generate
if (FEATURE_STORE_BUFFER!="NONE") begin : store_buffer_gen
   assign store_buffer_read = (state == IDLE) & store_buffer_write |
			      (state == IDLE) & !store_buffer_empty |
			      (state == WRITE) & (dbus_ack_i | !dbus_req_o) &
			      (!store_buffer_empty | store_buffer_write) &
			      !last_write |
			      (state == WRITE) & last_write &
			      store_buffer_write;

   mor1kx_store_buffer
     #(
       .DEPTH_WIDTH(OPTION_STORE_BUFFER_DEPTH_WIDTH),
       .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH)
       )
   mor1kx_store_buffer
     (
      .clk	(clk),
      .rst	(rst),

      .pc_i	(ctrl_epcr_i),
      .adr_i	(store_buffer_wadr),
      .dat_i	(lsu_sdat),
      .bsel_i	(dbus_bsel),
      .atomic_i	(ctrl_op_lsu_atomic_i),
      .write_i	(store_buffer_write),

      .pc_o	(store_buffer_epcr_o),
      .adr_o	(store_buffer_radr),
      .dat_o	(store_buffer_dat),
      .bsel_o	(store_buffer_bsel),
      .atomic_o	(store_buffer_atomic),
      .read_i	(store_buffer_read),

      .full_o	(store_buffer_full),
      .empty_o	(store_buffer_empty)
      );
end else begin
   assign store_buffer_epcr_o = ctrl_epcr_i;
   assign store_buffer_radr = store_buffer_wadr;
   assign store_buffer_dat = lsu_sdat;
   assign store_buffer_bsel = dbus_bsel;
   assign store_buffer_empty = 1'b1;

   reg store_buffer_full_r;
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       store_buffer_full_r <= 0;
     else if (store_buffer_write)
       store_buffer_full_r <= 1;
     else if (write_done)
       store_buffer_full_r <= 0;

   assign store_buffer_full = store_buffer_full_r & !write_done;
end
endgenerate
   assign store_buffer_wadr = dc_adr_match;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       dc_enable_r <= 0;
     else if (dc_enable_i & !dbus_req_o)
       dc_enable_r <= 1;
     else if (!dc_enable_i & !dc_refill)
       dc_enable_r <= 0;

   assign dc_enabled = dc_enable_i & dc_enable_r;
   assign dc_adr = padv_execute_i &
		   (exec_op_lsu_load_i | exec_op_lsu_store_i) ?
		   exec_lsu_adr_i : ctrl_lsu_adr_i;
   assign dc_adr_match = dmmu_enable_i ?
			 {dmmu_phys_addr[OPTION_OPERAND_WIDTH-1:2],2'b0} :
			 {ctrl_lsu_adr_i[OPTION_OPERAND_WIDTH-1:2],2'b0};

   assign dc_refill_allowed = !(ctrl_op_lsu_store_i | state == WRITE) &
			      !dc_snoop_hit & !snoop_valid;

generate
if (FEATURE_DATACACHE!="NONE") begin : dcache_gen
   wire dc_req = ctrl_op_lsu & dc_access & !access_done & !dbus_stall &
		   !(dbus_atomic & dbus_we & !atomic_reserve);
   if (OPTION_DCACHE_LIMIT_WIDTH == OPTION_OPERAND_WIDTH) begin
      assign dc_access =  ctrl_op_lsu_store_i | dc_enabled &
			 !(dmmu_cache_inhibit & dmmu_enable_i);
   end else if (OPTION_DCACHE_LIMIT_WIDTH < OPTION_OPERAND_WIDTH) begin
      assign dc_access = ctrl_op_lsu_store_i | dc_enabled &
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
   assign dc_we = exec_op_lsu_store_i & !exec_op_lsu_atomic_i & padv_execute_i |
		  dbus_atomic & dbus_we_o & !write_done |
		  ctrl_op_lsu_store_i & tlb_reload_busy & !tlb_reload_req;

   /* mor1kx_dcache AUTO_TEMPLATE (
	    .refill_o			(dc_refill),
	    .refill_req_o		(dc_refill_req),
	    .refill_done_o		(dc_refill_done),
            .cache_hit_o                (dc_hit),
	    .cpu_err_o			(dc_err),
	    .cpu_ack_o			(dc_ack),
	    .cpu_dat_o			(dc_ldat),
	    .spr_bus_dat_o		(spr_bus_dat_dc_o),
	    .spr_bus_ack_o		(spr_bus_ack_dc_o),
            .snoop_hit_o                (dc_snoop_hit),
	    // Inputs
	    .clk			(clk),
	    .rst			(rst),
	    .dc_dbus_err_i		(dbus_err),
	    .dc_enable_i		(dc_enabled),
	    .dc_access_i		(dc_access),
	    .cpu_dat_i			(lsu_sdat),
	    .cpu_adr_i			(dc_adr),
	    .cpu_adr_match_i		(dc_adr_match),
	    .cpu_req_i			(dc_req),
	    .cpu_we_i			(dc_we),
	    .cpu_bsel_i			(dc_bsel),
	    .refill_allowed		(dc_refill_allowed),
	    .wradr_i			(dbus_adr),
	    .wrdat_i			(dbus_dat_i),
	    .we_i			(dbus_ack_i),
            .snoop_valid_i              (snoop_valid),
    );*/

   mor1kx_dcache
     #(
       .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH),
       .OPTION_DCACHE_BLOCK_WIDTH(OPTION_DCACHE_BLOCK_WIDTH),
       .OPTION_DCACHE_SET_WIDTH(OPTION_DCACHE_SET_WIDTH),
       .OPTION_DCACHE_WAYS(OPTION_DCACHE_WAYS),
       .OPTION_DCACHE_LIMIT_WIDTH(OPTION_DCACHE_LIMIT_WIDTH),
       .OPTION_DCACHE_SNOOP(OPTION_DCACHE_SNOOP)
       )
   mor1kx_dcache
	   (/*AUTOINST*/
	    // Outputs
	    .refill_o			(dc_refill),		 // Templated
	    .refill_req_o		(dc_refill_req),	 // Templated
	    .refill_done_o		(dc_refill_done),	 // Templated
	    .cache_hit_o		(dc_hit_o),		 // Templated
	    .cpu_err_o			(dc_err),		 // Templated
	    .cpu_ack_o			(dc_ack),		 // Templated
	    .cpu_dat_o			(dc_ldat),		 // Templated
	    .snoop_hit_o		(dc_snoop_hit),		 // Templated
	    .spr_bus_dat_o		(spr_bus_dat_dc_o),	 // Templated
	    .spr_bus_ack_o		(spr_bus_ack_dc_o),	 // Templated
	    // Inputs
	    .clk			(clk),			 // Templated
	    .rst			(rst),			 // Templated
	    .dc_dbus_err_i		(dbus_err),		 // Templated
	    .dc_enable_i		(dc_enabled),		 // Templated
	    .dc_access_i		(dc_access),		 // Templated
	    .cpu_dat_i			(lsu_sdat),		 // Templated
	    .cpu_adr_i			(dc_adr),		 // Templated
	    .cpu_adr_match_i		(dc_adr_match),		 // Templated
	    .cpu_req_i			(dc_req),		 // Templated
	    .cpu_we_i			(dc_we),		 // Templated
	    .cpu_bsel_i			(dc_bsel),		 // Templated
	    .refill_allowed		(dc_refill_allowed),	 // Templated
	    .wradr_i			(dbus_adr),		 // Templated
	    .wrdat_i			(dbus_dat_i),		 // Templated
	    .we_i			(dbus_ack_i),		 // Templated
	    .snoop_adr_i		(snoop_adr_i[31:0]),
	    .snoop_valid_i		(snoop_valid),		 // Templated
	    .spr_bus_addr_i		(spr_bus_addr_i[15:0]),
	    .spr_bus_we_i		(spr_bus_we_i),
	    .spr_bus_stb_i		(spr_bus_stb_i),
	    .spr_bus_dat_i		(spr_bus_dat_i[OPTION_OPERAND_WIDTH-1:0]));
end else begin
   assign dc_access = 0;
   assign dc_refill = 0;
   assign dc_refill_done = 0;
   assign dc_refill_req = 0;
   assign dc_ack = 0;
   assign dc_err = 0;
   assign dc_bsel = 0;
   assign dc_we = 0;
   assign dc_snoop_hit = 0;
   assign dc_hit_o = 0;
   assign dc_ldat = 0;
end

endgenerate

generate
if (FEATURE_DMMU!="NONE") begin : dmmu_gen
   wire  [OPTION_OPERAND_WIDTH-1:0] virt_addr;
   wire 			    dmmu_spr_bus_stb;
   wire 			    dmmu_enable;

   assign virt_addr = dc_adr;

   // small hack to delay dmmu spr reads by one cycle
   // ideally the spr accesses should work so that the address is presented
   // in execute stage and the delayed data should be available in control
   // stage, but this is not how things currently work.
   assign dmmu_spr_bus_stb = spr_bus_stb_i & (!padv_ctrl_i | spr_bus_we_i);

   assign tlb_reload_pagefault_clear = !ctrl_op_lsu; // use pipeline_flush_i?

   assign dmmu_enable = dmmu_enable_i & !pipeline_flush_i;

   /* mor1kx_dmmu AUTO_TEMPLATE (
    .enable_i				(dmmu_enable),
    .phys_addr_o			(dmmu_phys_addr),
    .cache_inhibit_o			(dmmu_cache_inhibit),
    .op_store_i				(ctrl_op_lsu_store_i),
    .op_load_i				(ctrl_op_lsu_load_i),
    .tlb_miss_o				(tlb_miss),
    .pagefault_o			(pagefault),
    .tlb_reload_req_o			(tlb_reload_req),
    .tlb_reload_busy_o			(tlb_reload_busy),
    .tlb_reload_addr_o			(tlb_reload_addr),
    .tlb_reload_pagefault_o		(tlb_reload_pagefault),
    .tlb_reload_ack_i			(tlb_reload_ack),
    .tlb_reload_data_i			(tlb_reload_data),
    .tlb_reload_pagefault_clear_i	(tlb_reload_pagefault_clear),
    .spr_bus_dat_o			(spr_bus_dat_dmmu_o),
    .spr_bus_ack_o			(spr_bus_ack_dmmu_o),
    .spr_bus_stb_i			(dmmu_spr_bus_stb),
    .virt_addr_i			(virt_addr),
    .virt_addr_match_i			(ctrl_lsu_adr_i),
    ); */
   mor1kx_dmmu
     #(
       .FEATURE_DMMU_HW_TLB_RELOAD(FEATURE_DMMU_HW_TLB_RELOAD),
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
      .tlb_reload_req_o			(tlb_reload_req),	 // Templated
      .tlb_reload_busy_o		(tlb_reload_busy),	 // Templated
      .tlb_reload_addr_o		(tlb_reload_addr),	 // Templated
      .tlb_reload_pagefault_o		(tlb_reload_pagefault),	 // Templated
      .spr_bus_dat_o			(spr_bus_dat_dmmu_o),	 // Templated
      .spr_bus_ack_o			(spr_bus_ack_dmmu_o),	 // Templated
      // Inputs
      .clk				(clk),
      .rst				(rst),
      .enable_i				(dmmu_enable),		 // Templated
      .virt_addr_i			(virt_addr),		 // Templated
      .virt_addr_match_i		(ctrl_lsu_adr_i),	 // Templated
      .op_store_i			(ctrl_op_lsu_store_i),	 // Templated
      .op_load_i			(ctrl_op_lsu_load_i),	 // Templated
      .supervisor_mode_i		(supervisor_mode_i),
      .tlb_reload_ack_i			(tlb_reload_ack),	 // Templated
      .tlb_reload_data_i		(tlb_reload_data),	 // Templated
      .tlb_reload_pagefault_clear_i	(tlb_reload_pagefault_clear), // Templated
      .spr_bus_addr_i			(spr_bus_addr_i[15:0]),
      .spr_bus_we_i			(spr_bus_we_i),
      .spr_bus_stb_i			(dmmu_spr_bus_stb),	 // Templated
      .spr_bus_dat_i			(spr_bus_dat_i[OPTION_OPERAND_WIDTH-1:0]));
end else begin
   assign dmmu_cache_inhibit = 0;
   assign tlb_miss = 0;
   assign pagefault = 0;
   assign tlb_reload_busy = 0;
   assign tlb_reload_req = 0;
   assign tlb_reload_pagefault = 0;
end
endgenerate


/*----------------Formal Checking--------------*/

`ifdef FORMAL

`ifdef LSU
`define ASSUME assume
`else
`define ASSUME assert
`endif

   reg f_past_valid;
   initial f_past_valid = 1'b0;
   initial assume (rst);

   always @(posedge clk)
      f_past_valid <= 1'b1;
   always @(*)
      if (!f_past_valid)
         assume (rst);

//------------Assumptions on Inputs-------------

`ifdef LSU
   always @(posedge clk) begin
      if (f_past_valid && $past(exec_op_lsu_load_i) && !$past(rst)
          && $past(padv_ctrl_i) && !$past(pipeline_flush_i) && !rst)
         assume (ctrl_op_lsu_load_i);
      if (f_past_valid && $past(exec_op_lsu_store_i) && !$past(rst)
          && $past(padv_ctrl_i) && !$past(pipeline_flush_i) && !rst)
         assume (ctrl_op_lsu_store_i);
      if (f_past_valid && $past(exec_op_lsu_atomic_i) && !$past(rst)
          && $past(padv_ctrl_i) && !$past(pipeline_flush_i) && !rst)
         assume (ctrl_op_lsu_atomic_i);
      end
`endif

   always @(posedge clk) begin
      if (f_past_valid && !$past(rst)) begin
         `ASSUME ($onehot0({exec_op_lsu_load_i, exec_op_lsu_store_i}));
         `ASSUME ($onehot0({ctrl_op_lsu_store_i, ctrl_op_lsu_load_i}));
      end
   end

//-------------------Assertions-----------------

//------------------LSU Properties--------------

   //Based on ctrl_lsu_adr_i, requested data is put on output port of LSU
   always @(*)
      casex ({ctrl_lsu_zext_i, ctrl_lsu_length_i, ctrl_lsu_adr_i[1:0]})
            5'b11x00: assert (lsu_result_o == lsu_ldat);
            5'b10011: assert (lsu_result_o == {24'd0, lsu_ldat[7:0]});
            5'b10110: assert (lsu_result_o == {16'd0, lsu_ldat[15:0]});
            5'b00011: assert (lsu_result_o == {{24{lsu_ldat[7]}}, lsu_ldat[7:0]});
            5'b00110: assert (lsu_result_o == {{16{lsu_ldat[15]}}, lsu_ldat[15:0]});
      endcase

   always @(*)
      if (pipeline_flush_i)
         assert (!lsu_except_dpagefault_o &&
                 !lsu_except_dtlb_miss_o && !lsu_except_align_o);

   //For exceptions related to dmmu, dmmu should be enabled
   always @(*)
      if (lsu_except_dtlb_miss_o | lsu_except_dpagefault_o)
         assert (dmmu_enable_i);

   always @(posedge clk)
      if (f_past_valid && !$past(rst) && !$past(pipeline_flush_i)
          && !$past(padv_execute_i) && $past(dbus_err_i))
         assert (lsu_except_dbus_o);

//---------------LSU SPR Properties-----------------------

   always @(posedge clk)
      if (spr_bus_ack_dc_o && f_past_valid && !$past(rst) &&
          FEATURE_DMMU != "NONE" && FEATURE_DATACACHE != "NONE")
         assert (!spr_bus_ack_dmmu_o);

   //For spr read, dcache shouldn't acknowledge as dcache
   // won't support any read requests
   always @(posedge clk)
      if (dc_access && spr_bus_stb_i && !spr_bus_we_i &&
          !$past(spr_bus_we_i) && f_past_valid && !$past(rst))
       assert (!spr_bus_ack_dc_o);

   always @(posedge clk)
      if (f_past_valid && spr_bus_ack_dmmu_o)
         assert (spr_bus_we_i | !spr_bus_we_i);

//---------------DCACHE-----------------

   //Load
   //Case 1: If address is found in cache then cache hit is seen immediately
   // and data will be muxed to lsudat immediately if dbus_access is low.
   (* anyconst *) wire [OPTION_OPERAND_WIDTH-1:0] f_loaded_data;

   always @(posedge clk)
      if (f_past_valid && !$past(rst) && dc_ack && !dc_refill
          && dc_enabled && dc_access && ctrl_op_lsu_load_i &&
          !dbus_access && (dc_ldat == f_loaded_data)
          && ctrl_lsu_adr_i[1:0] == 2'd0 && ctrl_lsu_length_i == 2'd3) begin
         assert (dc_hit_o);
         assert (lsu_ack);
         assert (lsu_valid_o);
         assert (lsu_ldat == f_loaded_data);
         assert (lsu_result_o == f_loaded_data);
      end

   //Case 2: If address is found in cache then cache hit is seen immediately and
   // if dbus_access is high, then data is put on output port as soon as dbus_access goes low.

   always @(posedge clk)
      if (f_past_valid && !$past(rst) && $past(dc_ack) && !$past(dc_refill)
         && $past(dc_enabled) && $past(dc_access) && $past(ctrl_op_lsu_load_i)
         && ctrl_op_lsu_load_i && $past(dbus_access) && !$past(rst,2) && $past(state != WRITE) &&
         $past(dc_ldat) == f_loaded_data && !$past(dbus_ack) && (dc_ldat == f_loaded_data)
         && !dbus_access) begin
         assert($past(dc_hit_o));
         assert(!$past(lsu_ack));
         assert(lsu_ack);
         assert ($stable(lsu_ldat));
         assert(lsu_ldat == f_loaded_data);
      end

   //access_done will be high only if lsu_ack is high in previous clock
   always @(posedge clk)
      if (f_past_valid && !$past(rst) && $past(lsu_ack) && !$past(padv_execute_i)) begin
         assert (access_done);
         assert (lsu_valid_o);
      end

   /*/Fail: dmmu_cache_inhibit fails to inhibit dcache
   always @(posedge clk)
      if (dmmu_cache_inhibit && f_past_valid && !$past(rst) && !ctrl_op_lsu_store_i)
         assert (!dc_access);*/

   always @(*) begin
      if (dbus_burst_o)
         assert (state == DC_REFILL);
      if (dbus_access)
         assert (state != DC_REFILL);
   end

//----------------------DATA BUS-----------------------------
//Walk through memory load access

   (* anyconst *) wire [OPTION_OPERAND_WIDTH-1:0] f_adr;
   reg f_track_state = 0;
   initial f_track_state = 0;
   always @(posedge clk) begin

         if ($past(ctrl_op_lsu_load_i)
             && $past(store_buffer_empty) && !$past(dc_refill) && !$past(dbus_ack)
             && !$past(dbus_err) && !$past(except_dbus) && !$past(access_done) && $past(dbus_access)
             && !$past(pipeline_flush_i) && !$past(tlb_reload_req) && !$past(dmmu_enable_i)
             && !$past(except_align) && $past(ctrl_lsu_adr_i) == f_adr && f_past_valid && state == IDLE
             && !$past(rst) && $past(rst,2)) begin
             assert (dbus_req_o);
             assert (state == READ);
             assert (dbus_adr == f_adr);
             f_track_state <= 1;
         end

         if ($rose(f_track_state) && f_past_valid && $past(dbus_dat_i) == f_loaded_data
             && $past(dbus_ack_i) && !$past(rst)) begin
            assert (dbus_dat_o == f_loaded_data);
            assert (dbus_ack);
            assert (lsu_ack);
            assert (lsu_valid_o);
            assert (!dbus_burst_o);
     end
   end

   always @(posedge clk)
      if (f_past_valid && dbus_req_o && !$past(rst))
         assert (state != IDLE);

//----------------------LSU ACKS------------------------
//This code snippet checks if all store and load requests
//are acknowledged by lsu unit.Some load requests could be
//fulfilled immediately and some requests leads to refilling
//which might take maximum of 8 clock cycles to acknowledge.

   //Counts load requests
   reg [5:0]f_ld_reqs;
   initial f_ld_reqs = 0;
   //Counts store_requests
   reg [5:0]f_st_reqs;
   initial f_st_reqs = 0;

   always @(posedge clk)
      if (rst || pipeline_flush_i) begin
         f_ld_reqs <=0;
         f_st_reqs <=0;
      end
      else if (ctrl_op_lsu_load_i)
         f_ld_reqs <=f_ld_reqs+1;
      else if (ctrl_op_lsu_store_i)
         f_st_reqs <=f_st_reqs +1;

   //Counts acknowledgements
   reg [5:0]f_lsu_acks;
   initial f_lsu_acks = 0;

   always @(posedge clk) begin
      if (rst || pipeline_flush_i)
         f_lsu_acks <=0;
      else if (lsu_valid_o && lsu_ack)
         f_lsu_acks<= f_lsu_acks +1;
   end

   //Critical path taken by lsu_ack while refilling is 8 clk cycles.
   //To assert completed requests f_no_ips is used to make sure no
   // new requests arise during refilling.
   reg [5:0] f_no_ips;
   initial f_no_ips = 0;

   always @(posedge clk)
      if (rst || pipeline_flush_i)
         f_no_ips <=0;
      else if (f_past_valid && !ctrl_op_lsu && !$past(ctrl_op_lsu)
               && !$past(rst) && !$past(pipeline_flush_i) && !pipeline_flush_i)
         f_no_ips <= f_no_ips + 1;

   //Assert acks are sum of load and store requests
   always @(posedge clk)
      if (f_past_valid && !$past(rst) && $rose(f_no_ips) == 8)
         assert (f_lsu_acks == f_ld_reqs + f_st_reqs);

//----------------Store buffer Properties---------------------

   //Don't read from store buffer if store buffer is empty
   always @(posedge clk)
      if (store_buffer_empty && !store_buffer_write
          && f_past_valid && !$past(rst))
         assert (!store_buffer_read);

   //Assert store buffer can't be empty and full at the same time
   always @(*)
      if (store_buffer_full)
         assert (!store_buffer_empty);

   //No write when store buffer is full
   always @(*)
      if (store_buffer_full)
         assert (!store_buffer_write);

   //Store buffer ack implies buffer write was successful
   always @(*)
      if (store_buffer_ack)
         assert (store_buffer_write);

   always @(posedge clk)
      if (f_past_valid && !$past(rst) && !$past(pipeline_flush_i)
          && $past(dbus_err_i) && $past(dbus_we_o))
         assert (store_buffer_err_o);

   //Walk through store buffer
   (* anyconst *) wire [OPTION_OPERAND_WIDTH-1:0] f_pc;
   (* anyconst *) wire [OPTION_OPERAND_WIDTH-1:0] f_wadr;
   (* anyconst *) reg [OPTION_OPERAND_WIDTH-1:0] f_dat_i;
   (* anyconst *) wire [3:0] f_bsel;
   reg f_stored;
   initial f_stored = 0;

   //Queing incoming store info in buffer.
   always @(posedge clk)
      if (f_past_valid && !$past(rst) && (ctrl_epcr_i == f_pc)
          && store_buffer_wadr == f_wadr && f_dat_i == lsu_sdat
          && dbus_bsel == f_bsel && !ctrl_op_lsu_atomic_i &&
          store_buffer_write && store_buffer_empty)
          //Buffer has one entry
          f_stored <= 1;

   always @(posedge clk)
      if (f_past_valid && store_buffer_radr == f_wadr && !$past(rst)
          && $rose(f_stored) && $past(store_buffer_read) && !rst) begin
         assert (store_buffer_dat == f_dat_i);
         assert (store_buffer_epcr_o == f_pc);
         assert (store_buffer_bsel == f_bsel);
         assert (!store_buffer_atomic);
         //Poping this entry, makes buffer empty
         assert (store_buffer_empty);
      end

   //Writing all queued stores is completed if last buffer data is written
   always @(posedge clk)
      if (f_past_valid && !$past(rst) && write_done && !$past(dbus_err_i))
         assert ($past(last_write));

   //If there are any exceptions then store buffer shouldn't store anything.
   always @(*)
      if (except_align | except_dbus | except_dtlb_miss | except_dpagefault) begin
         assert (!store_buffer_write);
         assert (dbus_stall);
      end

   //While refilling don't write store buffer
   always @(*)
      if (dc_refill)
         assert (!store_buffer_write);

   //Don't allow refilling while doing store operation
   always @(*)
      if (ctrl_op_lsu_store_i || state == WRITE)
         assert (!dc_refill_allowed);

`endif
endmodule // mor1kx_lsu_cappuccino
