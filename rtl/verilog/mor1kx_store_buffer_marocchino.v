/////////////////////////////////////////////////////////////////////
//                                                                 //
//  mor1kx_store_buffer_marocchino                                 //
//                                                                 //
//  Description:                                                   //
//    Store buffer                                                 //
//    Tightly coupled with MAROCCHINO LSU                          //
//    Based on mor1kx_store_buffer                                 //
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

`include "mor1kx-defines.v"

module mor1kx_store_buffer_marocchino
#(
  parameter DEPTH_WIDTH          =  4, // 16 taps
  parameter OPTION_OPERAND_WIDTH = 32,
  parameter CLEAR_ON_INIT        = 0
)
(
  input                               clk,
  input                               rst,
  // entry port
  input    [OPTION_OPERAND_WIDTH-1:0] sbuf_epcr_i,
  input    [OPTION_OPERAND_WIDTH-1:0] virt_addr_i,
  input    [OPTION_OPERAND_WIDTH-1:0] phys_addr_i,
  input    [OPTION_OPERAND_WIDTH-1:0] dat_i,
  input  [OPTION_OPERAND_WIDTH/8-1:0] bsel_i,
  input                               write_i,
  // output port
  output   [OPTION_OPERAND_WIDTH-1:0] sbuf_epcr_o,
  output   [OPTION_OPERAND_WIDTH-1:0] virt_addr_o,
  output   [OPTION_OPERAND_WIDTH-1:0] phys_addr_o,
  output   [OPTION_OPERAND_WIDTH-1:0] dat_o,
  output [OPTION_OPERAND_WIDTH/8-1:0] bsel_o,
  input                               read_i,
  // status flags
  output                              full_o,
  output                              empty_o
);

  // The fifo stores (pc + virtual_address + physical_address + data + byte-sel)
  localparam FIFO_DATA_WIDTH = OPTION_OPERAND_WIDTH*4 +
                               OPTION_OPERAND_WIDTH/8;

  wire  [FIFO_DATA_WIDTH-1:0] fifo_dout;
  wire  [FIFO_DATA_WIDTH-1:0] fifo_din;

  reg         [DEPTH_WIDTH:0] write_pointer;
  wire        [DEPTH_WIDTH:0] write_pointer_next;
  
  reg         [DEPTH_WIDTH:0] read_pointer;
  wire        [DEPTH_WIDTH:0] read_pointer_next;

  // write pointer update
  assign write_pointer_next = write_pointer + {{DEPTH_WIDTH{1'b0}},1'b1};
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      write_pointer <= {(DEPTH_WIDTH+1){1'b0}};
    else if (write_i)
      write_pointer <= write_pointer_next;
  end

  // read pointer update
  assign read_pointer_next = read_pointer + {{DEPTH_WIDTH{1'b0}},1'b1};
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      read_pointer <= {(DEPTH_WIDTH+1){1'b0}};
    else if (read_i)
      read_pointer <= read_pointer_next;
  end

  // "buffer is full flag"
  assign full_o = (write_pointer_next[DEPTH_WIDTH] != read_pointer[DEPTH_WIDTH]) &
                  (write_pointer_next[DEPTH_WIDTH-1:0] == read_pointer[DEPTH_WIDTH-1:0]);

  // "buffer is empty flag"
  assign empty_o = (write_pointer == read_pointer);

  // data input/output
  assign fifo_din = {bsel_i, dat_i, phys_addr_i, virt_addr_i, sbuf_epcr_i};
  assign {bsel_o, dat_o, phys_addr_o, virt_addr_o, sbuf_epcr_o} = fifo_dout;


  // same addresses for read and write
  wire rw_same_addr = (read_pointer[DEPTH_WIDTH-1:0] == write_pointer[DEPTH_WIDTH-1:0]);

  // Read / Write port (*_rwp_*) controls
  wire rwp_we = write_i & read_i & rw_same_addr;

  // Write-only port (*_wp_*) controls
  wire wp_en  = write_i & (~read_i | ~rw_same_addr);

  // FIFO instance
  mor1kx_dpram_en_w1st_sclk
  #(
    .ADDR_WIDTH     (DEPTH_WIDTH),
    .DATA_WIDTH     (FIFO_DATA_WIDTH),
    .CLEAR_ON_INIT  (CLEAR_ON_INIT)
  )
  fifo_ram
  (
    // common clock
    .clk    (clk),
    // port "a": Read / Write (for RW-conflict case)
    .en_a   (read_i), // enable port "a"
    .we_a   (rwp_we), // operation is "write"
    .addr_a (read_pointer[DEPTH_WIDTH-1:0]),
    .din_a  (fifo_din),
    .dout_a (fifo_dout),
    // port "b": Write if no RW-conflict
    .en_b   (wp_en),  // enable port "b"
    .we_b   (write_i), // operation is "write"
    .addr_b (write_pointer[DEPTH_WIDTH-1:0]),
    .din_b  (fifo_din),
    .dout_b ()            // not used
  );

endmodule // mor1kx_store_buffer_marocchino
