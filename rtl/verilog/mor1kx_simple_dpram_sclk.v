/* ****************************************************************************
  SPDX-License-Identifier: CERN-OHL-W-2.0

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

/*--------------Formal checking---------------*/

`ifdef FORMAL

   reg f_past_valid;
   (* anyconst *) wire [ADDR_WIDTH-1:0] f_addr;
   (* anyconst *) reg [DATA_WIDTH-1:0] f_data;

   initial f_past_valid = 1'b0;
   always @(posedge clk)
      f_past_valid <= 1'b1;

`ifdef SDPRAM

   reg f_written = 0;
   initial f_written = 0;

   //Writing f_data at address f_addr
   always @(posedge clk)
      if (f_past_valid && $past(we) && $past(waddr) == f_addr && !ENABLE_BYPASS && $past(din) == f_data)
         f_written <= 1;

   //Read access for address f_addr should return f_data
   always @(posedge clk)
      if (f_past_valid && $past(re) && $past(raddr) == f_addr && !ENABLE_BYPASS && $rose(f_written))
        assert (dout == f_data);

`endif

   //Verifying Bypass logic of SDPRAM
   always @(posedge clk)
      if (f_past_valid && $past(we) && $past(re) && $past(waddr) == f_addr && $past(raddr) == f_addr && ENABLE_BYPASS)
        assert (dout == $past(din));

   //Output data should remain unchanged if there is no read enable
   always @(posedge clk)
      if (f_past_valid && !$past(re))
         assert ($stable(dout));

   //Output data changes only if there is read or write enable
   always @(posedge clk)
      if (f_past_valid && $changed(dout))
         assert ($past(re) | $past(we));
`endif

endmodule
