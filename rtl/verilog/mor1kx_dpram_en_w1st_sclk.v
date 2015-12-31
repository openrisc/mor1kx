/////////////////////////////////////////////////////////////////////
//                                                                 //
//  mor1kx_dpram_en_w1st_sclk                                      //
//                                                                 //
//  Description:                                                   //
//    Dual port RAM:                                               //
//      a) "enable" for both read & write for both ports           //
//      b) "write 1st": written value appears on output            //
//      c) "clear on init" feature for simulation                  //
//      d) common clock                                            //
//                                                                 //
//  Based on mor1kx_true_dpram_sclk                                //
//                                                                 //
/////////////////////////////////////////////////////////////////////
//                                                                 //
//   Copyright (C) 2013 Stefan Kristiansson                        //
//                      stefan.kristiansson@saunalahti.fi          //
//                                                                 //
//   Copyright (C) 2015 Andrey Bacherov                            //
//                      avbacherov@opencores.org                   //
//                                                                 //
//      This Source Code Form is subject to the terms of the       //
//      Open Hardware Description License, v. 1.0. If a copy       //
//      of the OHDL was not distributed with this file, You        //
//      can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt    //
//                                                                 //
/////////////////////////////////////////////////////////////////////

module mor1kx_dpram_en_w1st_sclk
#(
  parameter ADDR_WIDTH    = 32,
  parameter DATA_WIDTH    = 32,
  parameter CLEAR_ON_INIT =  0
)
(
  // common clock
  input                       clk,
  // port "a"
  input                       en_a,    // enable port "a"
  input                       we_a,    // operation is "write"
  input      [ADDR_WIDTH-1:0] addr_a,
  input      [DATA_WIDTH-1:0] din_a,
  output reg [DATA_WIDTH-1:0] dout_a,
  // port "b"
  input                       en_b,    // enable port "b"
  input                       we_b,    // operation is "write"
  input      [ADDR_WIDTH-1:0] addr_b,
  input      [DATA_WIDTH-1:0] din_b,
  output reg [DATA_WIDTH-1:0] dout_b
);

  reg [DATA_WIDTH-1:0] mem[0:((1<<ADDR_WIDTH)-1)];

  generate
  if (CLEAR_ON_INIT) begin : clear_ram
    integer idx;
    initial begin
      // clear output registers
      dout_a = {DATA_WIDTH{1'b0}};
      dout_b = {DATA_WIDTH{1'b0}};
      // clear memory array
      for (idx=0; idx < (1<<ADDR_WIDTH); idx=idx+1)
        mem[idx] = {DATA_WIDTH{1'b0}};
    end
  end
  endgenerate

  always @(posedge clk) begin
    if(en_a) begin
      if (we_a) begin
        mem[addr_a] <= din_a;
        dout_a      <= din_a;
      end
      else begin
        dout_a <= mem[addr_a];
      end // write / read
    end // enable
  end // @clock

  always @(posedge clk) begin
    if(en_b) begin
      if (we_b) begin
        mem[addr_b] <= din_b;
        dout_b      <= din_b;
      end
      else begin
        dout_b <= mem[addr_b];
      end // write / read
    end // enable
  end // @clock

endmodule // mor1kx_dpram_en_w1st_sclk
