/* ****************************************************************************
  SPDX-License-Identifier: CERN-OHL-W-2.0

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
    input 				atomic_i,
    input 				write_i,

    output [OPTION_OPERAND_WIDTH-1:0] 	pc_o,
    output [OPTION_OPERAND_WIDTH-1:0] 	adr_o,
    output [OPTION_OPERAND_WIDTH-1:0] 	dat_o,
    output [OPTION_OPERAND_WIDTH/8-1:0] bsel_o,
    output 				atomic_o,
    input 				read_i,

    output 				full_o,
    output 				empty_o
    );

   // The fifo stores address + data + byte sel + pc + atomic
   localparam FIFO_DATA_WIDTH = OPTION_OPERAND_WIDTH*3 +
				OPTION_OPERAND_WIDTH/8 + 1;

   wire [FIFO_DATA_WIDTH-1:0] 		fifo_dout;
   wire [FIFO_DATA_WIDTH-1:0] 		fifo_din;

   reg [DEPTH_WIDTH:0]                  write_pointer;
   reg [DEPTH_WIDTH:0]                  read_pointer;

   assign fifo_din = {adr_i, dat_i, bsel_i, pc_i, atomic_i};
   assign {adr_o, dat_o, bsel_o, pc_o, atomic_o} = fifo_dout;

   assign full_o = (write_pointer[DEPTH_WIDTH] != read_pointer[DEPTH_WIDTH]) &&
                   (write_pointer[DEPTH_WIDTH-1:0] == read_pointer[DEPTH_WIDTH-1:0]);
   assign empty_o = write_pointer == read_pointer;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       write_pointer <= 0;
     else if (write_i)
       write_pointer <= write_pointer + 1'd1;

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       read_pointer <= 0;
     else if (read_i)
       read_pointer <= read_pointer + 1'd1;

   mor1kx_simple_dpram_sclk
     #(
       .ADDR_WIDTH(DEPTH_WIDTH),
       .DATA_WIDTH(FIFO_DATA_WIDTH),
       .ENABLE_BYPASS(1)
       )
   fifo_ram
     (
      .clk			(clk),
      .dout			(fifo_dout),
      .raddr			(read_pointer[DEPTH_WIDTH-1:0]),
      .re			(read_i),
      .waddr			(write_pointer[DEPTH_WIDTH-1:0]),
      .we			(write_i),
      .din			(fifo_din)
      );

/*--------------Formal Checking--------------*/

`ifdef FORMAL

`ifdef BUFFER
`define ASSUME assume
`else
`define ASSUME assert
`endif

   reg f_past_valid;
   initial f_past_valid = 1'b0;
   always @(posedge clk)
      f_past_valid <= 1;
   always @(posedge clk)
      if (!f_past_valid)
         assume (rst);

   localparam f_total_fifo_entries = 2 ** DEPTH_WIDTH;
   wire [DEPTH_WIDTH:0]f_curr_fifo_entries;

   assign f_curr_fifo_entries = write_pointer - read_pointer;

   //Reset Assertions---------------->
   always @(posedge clk)
      if ($past(rst) && f_past_valid)
         assert ((write_pointer == 0) && (read_pointer == 0)
                 && empty_o && !full_o &&
                 (f_curr_fifo_entries == 0));

   //Full FIFO Assertions------------>
   //1. When FIFO is full, full flag should be set.
   always @(posedge clk `OR_ASYNC_RST)
      if (f_past_valid && f_curr_fifo_entries == f_total_fifo_entries)
         assert (full_o);

   //2. When fifo has f_total_fifo_entries-1 entries, and
   //   write_i occurs, then full_o has to be set.
   always @(posedge clk)
      if (f_past_valid && ($past(f_curr_fifo_entries) ==
          f_total_fifo_entries - 1) && $past(write_i) &&
          !$past(read_i) && !$past(rst))
         assert (full_o);

   //2. When FIFO is full, no write_i.
   always @(posedge clk) begin
      if (f_past_valid && full_o)
         `ASSUME (!write_i);
   end

   //Empty FIFO Assertions---------->
   //1. When FIFO has no entries, empty flag has to be set.
   always @(posedge clk)
      if (f_curr_fifo_entries == 0 && f_past_valid)
         assert (empty_o);

   //2. When FIFO has one entry, and read occurs, then empty flag should be set.
   always @(posedge clk)
      if ($past(f_curr_fifo_entries == 1) && f_past_valid
          && $past(read_i) && !$past(write_i))
         assert (empty_o);

   //3. When FIFO is empty, no read_i.
   always @(posedge clk)
      if (empty_o && f_past_valid && !write_i)
         `ASSUME (!read_i);

   //Empty flag and Full flag can't be 1 at the same time.
   always @(*)
         assert ($onehot0({empty_o, full_o}));

   //When FIFO is neither full nor empty, both full and empty flags should be 0.
   always @(posedge clk)
      if (f_curr_fifo_entries && (f_curr_fifo_entries
           < f_total_fifo_entries) && f_past_valid && !$past(rst))
         assert (!full_o && !empty_o);

   //Write pointer should not change when write_i is 0.
   always @(posedge clk)
      if (f_past_valid && !$past(write_i) && !$past(rst))
         assert ($stable(write_pointer));

   //Read pointer should not change when read_i is 0.
   always @(posedge clk)
      if (f_past_valid && !$past(read_i) && !$past(rst))
         assert ($stable(read_pointer));

`endif
endmodule
