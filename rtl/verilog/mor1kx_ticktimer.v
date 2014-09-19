/* ****************************************************************************
 This Source Code Form is subject to the terms of the
 Open Hardware Description License, v. 1.0. If a copy
 of the OHDL was not distributed with this file, You
 can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

 Description: mor1kx tick timer unit

 Copyright (C) 2012 Authors

 Author(s): Julius Baxter <juliusbaxter@gmail.com>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_ticktimer
  (
   input 	 clk,
   input 	 rst,

   output [31:0] spr_ttmr_o,
   output [31:0] spr_ttcr_o,

   // SPR Bus interface
   input         spr_access_i,
   input         spr_we_i,
   input [15:0]  spr_addr_i,
   input [31:0]  spr_dat_i,
   output        spr_bus_ack,
   output [31:0] spr_dat_o
   );

   // Registers
   reg [31:0]    spr_ttmr;
   reg [31:0]    spr_ttcr;

   wire spr_ttmr_access;
   wire spr_ttcr_access;

   // ttcr control wires
   wire          ttcr_clear;
   wire          ttcr_run;
   wire          ttcr_match;

   assign spr_ttmr_o = spr_ttmr;
   assign spr_ttcr_o = spr_ttcr;

   assign spr_ttmr_access =
     spr_access_i &
     (`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_TTMR_ADDR));
   assign spr_ttcr_access =
     spr_access_i &
     (`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_TTCR_ADDR));

   assign spr_bus_ack = spr_access_i;
   assign spr_dat_o = (spr_access_i & spr_ttcr_access) ? spr_ttcr :
                      (spr_access_i & spr_ttmr_access) ? spr_ttmr : 0;

   assign ttcr_match = spr_ttcr[27:0] == spr_ttmr[27:0];

   // Timer SPR control
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_ttmr <= 0;
     else if (spr_we_i & spr_ttmr_access)
       spr_ttmr <= spr_dat_i[31:0];
     else if (ttcr_match & spr_ttmr[29])
       spr_ttmr[28] <= 1; // Generate interrupt

   // Modes (spr_ttmr[31:30]):
   // 00 Tick timer is disabled.
   // 01 Timer is restarted on ttcr_match.
   // 10 Timer stops when ttcr_match is true.
   // 11 Timer does not stop when ttcr_match is true
   assign ttcr_clear = (spr_ttmr[31:30] == 2'b01) & ttcr_match;
   assign ttcr_run = (spr_ttmr[31:30] != 2'b00) & !ttcr_match |
		     (spr_ttmr[31:30] == 2'b11);

   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_ttcr <= 0;
     else if (spr_we_i & spr_ttcr_access)
       spr_ttcr <= spr_dat_i[31:0];
     else if (ttcr_clear)
       spr_ttcr <= 0;
     else if (ttcr_run)
       spr_ttcr <= spr_ttcr + 1;

endmodule // mor1kx_ticktimer
