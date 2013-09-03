/******************************************************************************
 This Source Code Form is subject to the terms of the
 Open Hardware Description License, v. 1.0. If a copy
 of the OHDL was not distributed with this file, You
 can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

 Description: Store buffer
 Currently a simple single clock FIFO, but with the ambition to
 have combining and reordering capabilities in the future.

 Copyright (C) 2013 Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>

 ******************************************************************************/
`include "mor1kx-defines.v"

module mor1kx_store_buffer
  #(
    parameter DEPTH_WIDTH = 4,
    parameter OPTION_OPERAND_WIDTH = 32
    )
   (
    input 				clk,
    input 				rst,

    input [OPTION_OPERAND_WIDTH-1:0] 	pc_i,
    input [OPTION_OPERAND_WIDTH-1:0] 	adr_i,
    input [OPTION_OPERAND_WIDTH-1:0] 	dat_i,
    input [OPTION_OPERAND_WIDTH/8-1:0] 	bsel_i,
    input 				write_i,

    output [OPTION_OPERAND_WIDTH-1:0] 	pc_o,
    output [OPTION_OPERAND_WIDTH-1:0] 	adr_o,
    output [OPTION_OPERAND_WIDTH-1:0] 	dat_o,
    output [OPTION_OPERAND_WIDTH/8-1:0] bsel_o,
    input 				read_i,

    output 				full_o,
    output 				empty_o
    );

   // The fifo stores address + data + byte sel + pc
   localparam FIFO_DATA_WIDTH = OPTION_OPERAND_WIDTH*3 + OPTION_OPERAND_WIDTH/8;

   wire [FIFO_DATA_WIDTH-1:0] 		fifo_dout;
   reg [FIFO_DATA_WIDTH-1:0] 		fifo_dout_r;
   wire [FIFO_DATA_WIDTH-1:0] 		fifo_din;

   wire [DEPTH_WIDTH-1:0] 		fifo_raddr;

   reg [DEPTH_WIDTH-1:0] 		write_pointer;
   reg [DEPTH_WIDTH-1:0] 		read_pointer;
   wire [DEPTH_WIDTH-1:0] 		prev_read_pointer;

   reg 					read_r;

   assign fifo_din = {adr_i, dat_i, bsel_i, pc_i};
   assign {adr_o, dat_o, bsel_o, pc_o} = read_r ? fifo_dout : fifo_dout_r;

   assign prev_read_pointer = read_pointer - 1;

   assign full_o = write_pointer == prev_read_pointer;
   assign empty_o = write_pointer == read_pointer;

   assign fifo_raddr = read_pointer;

   // TODO: add read enable to RAM?
   always @(posedge clk)
     read_r <= read_i;

   always @(posedge clk)
     if (read_r)
       fifo_dout_r <= fifo_dout;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       write_pointer <= 0;
     else if (write_i)
       write_pointer <= write_pointer + 1;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       read_pointer <= 0;
     else if (read_i)
       read_pointer <= read_pointer + 1;

   mor1kx_simple_dpram_sclk
     #(
       .ADDR_WIDTH(DEPTH_WIDTH),
       .DATA_WIDTH(FIFO_DATA_WIDTH),
       .ENABLE_BYPASS("TRUE")
       )
   fifo_ram
     (
      .clk			(clk),
      .dout			(fifo_dout),
      .raddr			(fifo_raddr),
      .waddr			(write_pointer),
      .we			(write_i),
      .din			(fifo_din)
      );

endmodule
