/******************************************************************************
 This Source Code Form is subject to the terms of the
 Open Hardware Description License, v. 1.0. If a copy
 of the OHDL was not distributed with this file, You
 can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

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

//Formal Checking

`define ASSUME assert
`define ASSUME assume

`ifdef Formal

// Checking synchronous read and write operation at port A with clock_a 

always @(posedge clk_a) begin

if (we_a)
 assert ((din_a==mem[addr_a]) && (dout_a==din_a));
 
else begin
 assume (mem[addr_a]==32'hc032);
 //Assume some data at addr_a, check if same data is put on data port during read operation
 assert (dout_a==32'hc032);

end
end

//Checking synchronous read and write operation at port B with clock_b

always @(posedge clk_b) begin
 
if (we_b)
 assert ((din_b==mem[addr_b]) && (dout_b==din_b)));
 
else begin
 assume (mem[addr_b]==32'hbb20);
 //Assume some data at addr_b, check if same data is put on data port during read operation
 assert (dout_b==32'hbb20);
end
end

`endif

endmodule
