/* ****************************************************************************
  This Source Code Form is subject to the terms of the
  Open Hardware Description License, v. 1.0. If a copy
  of the OHDL was not distributed with this file, You
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: mor1kx processor avalon bus bridge

  Copyright (C) 2013 Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_bus_if_avalon
#(
  parameter OPTION_AVALON_BURST_LENGTH = 4
  )
  (
   input 	 clk,
   input 	 rst,

   output 	 cpu_err_o,
   output 	 cpu_ack_o,
   output [31:0] cpu_dat_o,
   input [31:0]  cpu_adr_i,
   input [31:0]  cpu_dat_i,
   input 	 cpu_req_i,
   input [3:0] 	 cpu_bsel_i,
   input 	 cpu_we_i,
   input 	 cpu_burst_i,

   output [31:0] avm_address_o,
   output [3:0]  avm_byteenable_o,
   output 	 avm_read_o,
   input [31:0]  avm_readdata_i,
   output [3:0]  avm_burstcount_o,
   output 	 avm_write_o,
   output [31:0] avm_writedata_o,
   input 	 avm_waitrequest_i,
   input 	 avm_readdatavalid_i
   );

   localparam IDLE	= 4'b0001;
   localparam READ	= 4'b0010;
   localparam BURST	= 4'b0100;
   localparam WRITE	= 4'b1000;

   reg [3:0] 	 state;

   always @(posedge clk) begin
      case (state)
	IDLE: begin
	   if (cpu_req_i & !avm_waitrequest_i) begin
	      if (cpu_we_i)
		state <= WRITE;
	      else if (cpu_burst_i) begin
		state <= BURST;
	      end else
		state <= READ;
	   end
	end

	READ: begin
	   if (avm_readdatavalid_i)
	     state <= IDLE;
	end

	BURST: begin
	   /* cpu_burst_i deasserts when the last burst access starts */
	   if (!cpu_burst_i & avm_readdatavalid_i)
	     state <= IDLE;
	end

	WRITE: begin
	     state <= IDLE;
	end
      endcase
   end

   assign avm_address_o = cpu_adr_i;
   assign avm_read_o = cpu_req_i & !cpu_we_i & (state == IDLE);
   assign avm_byteenable_o = cpu_bsel_i;
   assign avm_write_o = cpu_req_i & cpu_we_i & (state == IDLE);
   assign avm_burstcount_o = cpu_burst_i & (state != BURST) ?
			     OPTION_AVALON_BURST_LENGTH : 4'd1;
   assign avm_writedata_o = cpu_dat_i;

   assign cpu_err_o = 0;
   assign cpu_ack_o = avm_readdatavalid_i | state == WRITE;
   assign cpu_dat_o = avm_readdata_i;


endmodule
