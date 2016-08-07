////////////////////////////////////////////////////////////////////////
//                                                                    //
//  mor1kx_ticktimer_oneself                                          //
//                                                                    //
//  Description:                                                      //
//    - mor1kx tick timer unit decoupled from CTRL module             //
//    - derived from mor1kx_ticktimer originally designed by          //
//      Julius Baxter                                                 //
//    - 1st usage is planned for MAROCCHINO pipeline                  //
//                                                                    //
////////////////////////////////////////////////////////////////////////
//                                                                    //
//   Copyright (C) 2012 Julius Baxter                                 //
//                      juliusbaxter@gmail.com                        //
//                                                                    //
//   Copyright (C) 2016 Andrey Bacherov                               //
//                      avbacherov@opencores.org                      //
//                                                                    //
//      This Source Code Form is subject to the terms of the          //
//      Open Hardware Description License, v. 1.0. If a copy          //
//      of the OHDL was not distributed with this file, You           //
//      can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt       //
//                                                                    //
////////////////////////////////////////////////////////////////////////

`include "mor1kx-defines.v"

module mor1kx_ticktimer_oneself
(
  // clock and reset
  input             clk,
  input             rst,

  // ready flag
  output            tt_rdy_o,

  // SPR interface
  input      [15:0] spr_bus_addr_i,
  input             spr_bus_we_i,
  input             spr_bus_stb_i,
  input      [31:0] spr_bus_dat_i,
  output reg [31:0] spr_bus_dat_tt_o,
  output reg        spr_bus_ack_tt_o
);

  // Registers
  reg [31:0] spr_ttmr;
  reg [31:0] spr_ttcr;

  // SPR BUS
  wire spr_tt_cs = spr_bus_stb_i & (`SPR_BASE(spr_bus_addr_i) == `OR1K_SPR_TT_BASE);
  wire spr_tt_we = spr_tt_cs &  spr_bus_we_i;
  wire spr_tt_re = spr_tt_cs & ~spr_bus_we_i;

  wire spr_ttmr_cs = (`SPR_OFFSET(spr_bus_addr_i) == `SPR_OFFSET(`OR1K_SPR_TTMR_ADDR));
  wire spr_ttcr_cs = (`SPR_OFFSET(spr_bus_addr_i) == `SPR_OFFSET(`OR1K_SPR_TTCR_ADDR));

  reg spr_tt_we_r;

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      spr_tt_we_r       <= 1'b0;
      spr_bus_ack_tt_o  <= 1'b0;
      spr_bus_dat_tt_o  <= 32'd0;
    end
    else if (spr_bus_ack_tt_o) begin
      spr_tt_we_r       <= 1'b0;
      spr_bus_ack_tt_o  <= 1'b0;
      spr_bus_dat_tt_o  <= 32'd0;
    end
    else begin
      if (spr_tt_we) begin
        spr_tt_we_r       <= 1'b1;
        spr_bus_ack_tt_o  <= 1'b1;
        spr_bus_dat_tt_o  <= 32'd0;
      end
      else if (spr_tt_re) begin
        spr_tt_we_r       <= 1'b0;
        spr_bus_ack_tt_o  <= 1'b1;
        spr_bus_dat_tt_o  <= spr_ttmr_cs ? spr_ttmr :
                             spr_ttcr_cs ? spr_ttcr :
                                           32'd0;
      end
    end
  end // at clock


  // Timer
  assign tt_rdy_o = spr_ttmr[28];

  wire ttcr_match = (spr_ttcr[27:0] == spr_ttmr[27:0]);

  // Timer SPR control
  always @(posedge clk `OR_ASYNC_RST)
    if (rst)
      spr_ttmr <= 1'b0;
    else if (spr_tt_we_r & spr_ttmr_cs)
      spr_ttmr <= spr_bus_dat_i[31:0];
    else if (ttcr_match & spr_ttmr[29])
      spr_ttmr[28] <= 1'b1; // Generate interrupt

  // Modes (spr_ttmr[31:30]):
  // 00 Tick timer is disabled.
  // 01 Timer is restarted on ttcr_match.
  // 10 Timer stops when ttcr_match is true.
  // 11 Timer does not stop when ttcr_match is true
  wire ttcr_clear = ((spr_ttmr[31:30] == 2'b01) &  ttcr_match);
  wire ttcr_run   = ((spr_ttmr[31:30] != 2'b00) & ~ttcr_match) |
                     (spr_ttmr[31:30] == 2'b11);

  always @(posedge clk `OR_ASYNC_RST)
    if (rst)
      spr_ttcr <= 32'd0;
    else if (spr_tt_we_r & spr_ttcr_cs)
      spr_ttcr <= spr_bus_dat_i[31:0];
    else if (ttcr_clear)
      spr_ttcr <= 32'd0;
    else if (ttcr_run)
      spr_ttcr <= spr_ttcr + 32'd1;

endmodule // mor1kx_ticktimer_oneself
