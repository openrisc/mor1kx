/******************************************************************************
 This Source Code Form is subject to the terms of the
 Open Hardware Description License, v. 1.0. If a copy
 of the OHDL was not distributed with this file, You
 can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

 Description: Dual port ram with single clock

 Copyright (C) 2013 Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>

 ******************************************************************************/

module mor1kx_dpram_sclk
  #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
    )
   (
    input 		    clk,
    input [ADDR_WIDTH-1:0]  addr_a,
    input 		    we_a,
    input [DATA_WIDTH-1:0]  din_a,
    output [DATA_WIDTH-1:0] dout_a,
    input [ADDR_WIDTH-1:0]  addr_b,
    input 		    we_b,
    input [DATA_WIDTH-1:0]  din_b,
    output [DATA_WIDTH-1:0] dout_b
    );

   reg [DATA_WIDTH-1:0]     mem[(1<<ADDR_WIDTH)-1:0];

   reg [ADDR_WIDTH-1:0]     addr_a_r;
   reg [ADDR_WIDTH-1:0]     addr_b_r;

   assign dout_a = mem[addr_a_r];
   assign dout_b = mem[addr_b_r];

   always @(posedge clk) begin
      if (we_a)
	mem[addr_a] <= din_a;
      addr_a_r <= addr_a;
   end

   always @(posedge clk) begin
      if (we_b)
	mem[addr_b] <= din_b;
      addr_b_r <= addr_b;
   end

endmodule
