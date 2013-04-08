/* ****************************************************************************
  This Source Code Form is subject to the terms of the
  Open Hardware Description License, v. 1.0. If a copy
  of the OHDL was not distributed with this file, You
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: mor1kx processor Wishbone bus bridge

  For now, very simple, not registering,  assumes 32-bit data, addressing

  Copyright (C) 2012 Authors

  Author(s): Julius Baxter <juliusbaxter@gmail.com>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_bus_if_wb32
  (/*AUTOARG*/
   // Outputs
   cpu_err_o, cpu_ack_o, cpu_dat_o, wbm_adr_o, wbm_stb_o, wbm_cyc_o,
   wbm_sel_o, wbm_we_o, wbm_cti_o, wbm_bte_o, wbm_dat_o,
   // Inputs
   clk, rst, cpu_adr_i, cpu_dat_i, cpu_req_i, cpu_bsel_i, cpu_we_i,
   cpu_burst_i, wbm_err_i, wbm_ack_i, wbm_dat_i, wbm_rty_i
   );

   input clk, rst;

   output cpu_err_o;
   output cpu_ack_o;
   output [31:0] cpu_dat_o;
   input [31:0]  cpu_adr_i;
   input [31:0]  cpu_dat_i;
   input 	 cpu_req_i;
   input [3:0] 	 cpu_bsel_i;
   input  	 cpu_we_i;
   input 	 cpu_burst_i;

   output [31:0] wbm_adr_o;
   output 	 wbm_stb_o;
   output 	 wbm_cyc_o;
   output [3:0]  wbm_sel_o;
   output 	 wbm_we_o;
   output [2:0]  wbm_cti_o;
   output [1:0]  wbm_bte_o;
   output [31:0] wbm_dat_o;
   input 	 wbm_err_i;
   input 	 wbm_ack_i;
   input [31:0]  wbm_dat_i;
   input 	 wbm_rty_i;

   parameter BUS_IF_TYPE = "CLASSIC";

   parameter  burst_length = 8;
   parameter  baddr_with = (burst_length==4) ? 2 :
			   (burst_length==8) ? 3 :
			   (burst_length==16)? 4 : 30;

   initial
     $display("%m: Wishbone bus IF is %s",BUS_IF_TYPE);

   generate
      /* verilator lint_off WIDTH */
      if (BUS_IF_TYPE=="B3_READ_BURSTING") begin : b3_read_bursting
	 /* verilator lint_on WIDTH */

	 // Burst until the incoming address is not what it should be
	 wire 			      finish_burst;
	 reg 			      finish_burst_r;
	 reg 			      bursting;
	 reg [31:2] 		      burst_address;
	 reg [baddr_with-1:0]	      burst_wrap_start;
	 wire [baddr_with-1:0]	      burst_wrap_finish;
	 wire 			      address_differs;

	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     bursting <= 0;
	   else if (wbm_err_i)
	     bursting <= 0;
	   else if (bursting & finish_burst & wbm_ack_i)
	     bursting <= 0;
	   else if (cpu_req_i & !bursting & !cpu_we_i)
	     bursting <= 1;

	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     begin
		burst_address <= 0;
		burst_wrap_start <= 0;
	     end
	   else if (cpu_req_i & !bursting)
	     begin
		burst_address <= cpu_adr_i[31:2];
		burst_wrap_start <= cpu_adr_i[baddr_with+2-1:2];
	     end
	   else if (wbm_ack_i)
	     burst_address[baddr_with+2-1:2] <= burst_address[baddr_with+2-1:2]
		  + 1;


	 assign address_differs = (burst_address!=cpu_adr_i[31:2]);
	 assign burst_wrap_finish = burst_wrap_start - 1;
	 assign finish_burst = (bursting & (
		      (burst_length!=0 &&
		       burst_address[baddr_with+2-1:2]==(burst_wrap_finish))
					    | address_differs
					    | !cpu_req_i
					    )
				)
	   ;
	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     finish_burst_r <= 0;
	   else if (wbm_ack_i)
	     finish_burst_r <= finish_burst;
	   else
	     finish_burst_r <= 0;

	 assign wbm_adr_o = bursting ? {burst_address,2'b00} : cpu_adr_i;
	 assign wbm_stb_o = bursting & !finish_burst_r;
	 assign wbm_cyc_o = bursting & !finish_burst_r;
	 assign wbm_sel_o = cpu_bsel_i;
	 assign wbm_we_o = cpu_we_i;
	 assign wbm_cti_o = bursting ? (finish_burst ? 3'b111 : 3'b010) :
			    3'b000;
	 assign wbm_bte_o = burst_length==4  ? 2'b01 :
			    burst_length==8  ? 2'b10 :
			    burst_length==16 ? 2'b11 :
			    2'b00; // Linear burst

	 assign wbm_dat_o = cpu_dat_i;

	 assign cpu_err_o = wbm_err_i;
	 assign cpu_ack_o = (wbm_ack_i) &
			    !(bursting & address_differs) & cpu_req_i;
	 assign cpu_dat_o = wbm_err_i ? 0 :  wbm_dat_i;

      /* verilator lint_off WIDTH */
      end else if (BUS_IF_TYPE=="B3_REGISTERED_FEEDBACK") begin : b3_registered_feedback
	 /* verilator lint_on WIDTH */

	 assign wbm_adr_o = cpu_adr_i;
	 assign wbm_stb_o = cpu_req_i;
	 assign wbm_cyc_o = cpu_req_i;
	 assign wbm_sel_o = cpu_bsel_i;
	 assign wbm_we_o = cpu_we_i;
	 assign wbm_cti_o = cpu_burst_i ? 3'b010 : 3'b111;
	 assign wbm_bte_o = burst_length==4  ? 2'b01 :
			    burst_length==8  ? 2'b10 :
			    burst_length==16 ? 2'b11 :
			    2'b00; // Linear burst

	 assign wbm_dat_o = cpu_dat_i;
	 assign cpu_err_o = wbm_err_i;
	 assign cpu_ack_o = wbm_ack_i;
	 assign cpu_dat_o = wbm_dat_i;

      end else begin : classic // CLASSIC only

	 // Only classic, single cycle accesses

	 // A register to force de-assertion of access request signals after
	 // each ack
	 reg 				      cycle_end;

	 always @(posedge clk `OR_ASYNC_RST)
	   if (rst)
	     cycle_end <= 1;
	   else
	     cycle_end <= wbm_ack_i | wbm_err_i;

	 assign cpu_err_o = wbm_err_i;
	 assign cpu_ack_o = wbm_ack_i;
	 assign cpu_dat_o = wbm_dat_i;

	 assign wbm_adr_o = cpu_adr_i;
	 assign wbm_stb_o = cpu_req_i & !cycle_end;
	 assign wbm_cyc_o = cpu_req_i;
	 assign wbm_sel_o = cpu_bsel_i;
	 assign wbm_we_o = cpu_we_i;
	 assign wbm_cti_o = 0;
	 assign wbm_bte_o = 0;
	 assign wbm_dat_o = cpu_dat_i;

      end // else: !if(BUS_IF_TYPE=="READ_B3_BURSTING")
   endgenerate

endmodule // mor1kx_bus_if_wb
