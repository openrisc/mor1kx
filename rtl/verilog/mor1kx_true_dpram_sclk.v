/* ****************************************************************************
  SPDX-License-Identifier: CERN-OHL-W-2.0

  Description: True dual port ram with dual clock's

  Copyright (C) 2013 Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>

 ******************************************************************************/

module mor1kx_true_dpram_sclk
  #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
    )
   (
    /* Port A */
    input                   clk_a,
    input [ADDR_WIDTH-1:0]  addr_a,
    input                   we_a,
    input [DATA_WIDTH-1:0]  din_a,
    output [DATA_WIDTH-1:0] dout_a,

    /* Port B */
    input                   clk_b,
    input [ADDR_WIDTH-1:0]  addr_b,
    input                   we_b,
    input [DATA_WIDTH-1:0]  din_b,
    output [DATA_WIDTH-1:0] dout_b
    );

   reg [DATA_WIDTH-1:0]     mem[(1<<ADDR_WIDTH)-1:0];

   reg [DATA_WIDTH-1:0]     rdata_a;
   reg [DATA_WIDTH-1:0]     rdata_b;

   assign dout_a = rdata_a;
   assign dout_b = rdata_b;

   always @(posedge clk_a) begin
      if (we_a) begin
         mem[addr_a] <= din_a;
         rdata_a <= din_a;
      end else begin
         rdata_a <= mem[addr_a];
      end
   end

   always @(posedge clk_b) begin
      if (we_b) begin
         mem[addr_b] <= din_b;
         rdata_b <= din_b;
      end else begin
         rdata_b <= mem[addr_b];
      end
   end

/*-----------------Formal Checking------------------*/

`ifdef FORMAL

   reg f_past_valid;
   (* gclk *) reg global_clock;
   initial f_past_valid = 1'b0;

   always @(posedge global_clock)
      f_past_valid <= 1'b1;

`ifdef TDPRAM
`define ASSUME assume
`else
`define ASSUME assert
`endif

`ifdef TDPRAM

   always @(*)
      `ASSUME (addr_a != addr_b);

   (* anyconst *) wire [ADDR_WIDTH-1:0] f_addr;
   (* anyconst *) reg [DATA_WIDTH-1:0] f_data_a;
   (* anyconst *) reg [DATA_WIDTH-1:0] f_data_b;

   reg f_write_a = 0;
   initial f_write_a = 0;
   reg f_write_b = 0;
   initial f_write_b = 0;

   always @(posedge global_clock) begin

      if ($rose(clk_a)) begin
         //Port A: Writing f_data_a at address f_addr
         if ($past(we_a) && $past(addr_a) == f_addr && $past(din_a) == f_data_a && f_past_valid) begin
            assert (dout_a == f_data_a);
            f_write_a <= 1;
         end
         //Port A: Reading data from address f_addr
         if (!$past(we_a) && $past(addr_a) == f_addr && f_past_valid && $rose(f_write_a))
            assert (dout_a == f_data_a);
      end

      if ($rose(clk_b)) begin
         //Port B: Writing f_data_b at address f_addr
         if ($past(we_b) && $past(addr_b) == f_addr && $past(din_b) == f_data_b && f_past_valid) begin
            assert (dout_b == f_data_b);
            f_write_b <= 1;
         end
         //Port B: Writing f_data_b at address f_addr
         if (!$past(we_b) && $past(addr_b) == f_addr && f_past_valid && $rose(f_write_b))
            assert (dout_b == f_data_b);
      end
   end

`endif

   //Port A output data changes only if there is read or write access at port A
   always @(posedge clk_a)
      if (f_past_valid && $changed(dout_a))
         assert ($past(we_a) | !$past(we_a));

   //Port B output data changes only if there is read or write access at port B
   always @(posedge clk_b)
      if (f_past_valid && $changed(dout_b))
         assert ($past(we_b) | !$past(we_b));

   //Port B shouldn't be affected by write signals of port A
   always @(posedge global_clock)
      if (f_past_valid && $rose(clk_a) && $fell(clk_b) && $past(we_a))
         assert ($stable(dout_b));

   //Port A shouldn't be affected by write signals of port B
   always @(posedge global_clock)
      if (f_past_valid && $rose(clk_b) && $fell(clk_a) && $past(we_b))
         assert ($stable(dout_a));

`endif
endmodule
