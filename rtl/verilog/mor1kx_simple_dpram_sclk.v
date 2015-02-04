/******************************************************************************
 This Source Code Form is subject to the terms of the
 Open Hardware Description License, v. 1.0. If a copy
 of the OHDL was not distributed with this file, You
 can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

 Description:
 Simple single clocked dual port ram (separate read and write ports),
 with optional bypass logic.

 Copyright (C) 2012 Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>

 ******************************************************************************/

module mor1kx_simple_dpram_sclk
  #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32,
    parameter CLEAR_ON_INIT = 0,
    parameter ENABLE_BYPASS = 1
    )
   (
    input 		    clk,
    input [ADDR_WIDTH-1:0]  raddr,
    input 		    re,
    input [ADDR_WIDTH-1:0]  waddr,
    input 		    we,
    input [DATA_WIDTH-1:0]  din,
    output [DATA_WIDTH-1:0] dout
    );

   reg [DATA_WIDTH-1:0]     mem[(1<<ADDR_WIDTH)-1:0];
   reg [DATA_WIDTH-1:0]     rdata;

generate
if(CLEAR_ON_INIT) begin :clear_on_init
   integer 		    idx;
   initial
     for(idx=0; idx < (1<<ADDR_WIDTH); idx=idx+1)
       mem[idx] = {DATA_WIDTH{1'b0}};
end
endgenerate

generate
if (ENABLE_BYPASS) begin : bypass_gen
   reg [DATA_WIDTH-1:0]     din_r;
   reg 			    bypass;

   assign dout = bypass ? din_r : rdata;

   always @(posedge clk)
     if (re)
       din_r <= din;

   always @(posedge clk)
     if (waddr == raddr && we && re)
       bypass <= 1;
     else if (re)
       bypass <= 0;
end else begin
   assign dout = rdata;
end
endgenerate

   always @(posedge clk) begin
      if (we)
	mem[waddr] <= din;
      if (re)
	rdata <= mem[raddr];
   end

endmodule
