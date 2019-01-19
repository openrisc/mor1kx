////////////////////////////////////////////////////////////////////////
//                                                                    //
//  mor1kx_ticktimer_marocchino                                       //
//                                                                    //
//  Description:                                                      //
//    - Mor1kx tick timer unit decoupled from CTRL module.            //
//    - Derived from mor1kx_ticktimer originally designed by          //
//      Julius Baxter.                                                //
//    - It is operate  in Wishbone BUS clock domain.                  //
//      Wishbone BUS clock domain is useful for bacward compatibility //
//      with already compiled applications and toolchains.            //
//    - Actually, CDC is not implemented completely yet.              //
//      The CPU clock could be greater or equal to Wishbone one,      //
//      buth them must be aligned. So, synchronizers consist of       //
//      single latch named "*_r2". To implement full synchronizers    //
//      latches *_r1 shuld be appropriatelly added.                   //
//                                                                    //
////////////////////////////////////////////////////////////////////////
//                                                                    //
//   Copyright (C) 2012 Julius Baxter                                 //
//                      juliusbaxter@gmail.com                        //
//                                                                    //
//   Copyright (C) 2017-2018 Andrey Bacherov                          //
//                           avbacherov@opencores.org                 //
//                                                                    //
//      This Source Code Form is subject to the terms of the          //
//      Open Hardware Description License, v. 1.0. If a copy          //
//      of the OHDL was not distributed with this file, You           //
//      can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt       //
//                                                                    //
////////////////////////////////////////////////////////////////////////

`include "mor1kx-defines.v"

module mor1kx_ticktimer_marocchino
(
  // Wishbone side clock and reset
  input             wb_clk,
  input             wb_rst,

  // CPU side clock and reset
  input             cpu_clk,
  input             cpu_rst,

  // ready flag
  output reg        tt_rdy_o,

  // SPR interface
  input      [15:0] spr_bus_addr_i,
  input             spr_bus_we_i,
  input             spr_bus_stb_i,
  input             spr_bus_toggle_i,
  input      [31:0] spr_bus_dat_i,
  output reg [31:0] spr_bus_dat_tt_o,
  output reg        spr_bus_ack_tt_o
);

  // Timer's registers
  reg [31:0] spr_ttmr;
  reg [31:0] spr_ttcr;


  //---------------//
  // SPR interface //
  //---------------//

  //  we don't expect R/W-collisions for SPRbus vs Write-Back cycles since
  //    SPRbus access start 1-clock later than Write-Back
  //    thanks to MT(F)SPR processing logic (see OMAN)

  // CPU -> Wishbone clock domain

  // Pseudo CDC disclaimer:
  // As positive edges of wb-clock and cpu-clock assumed be aligned,
  // we use simplest clock domain pseudo-synchronizers.

  // Registering SPR BUS incoming signals in Wishbone clock domain.
  reg         spr_bus_stb_r1;
  reg         spr_bus_we_r1;
  reg  [14:0] spr_bus_addr_r1;
  reg  [31:0] spr_bus_dat_r1;
  // ---
  always @(posedge wb_clk) begin
    spr_bus_stb_r1  <= spr_bus_stb_i;
    spr_bus_we_r1   <= spr_bus_we_i;
    spr_bus_addr_r1 <= spr_bus_addr_i[14:0];
    spr_bus_dat_r1  <= spr_bus_dat_i;
  end // at wb-clock

  // Detect new SPR request in Wishbone clock domain.
  reg  cpu2tt_r1;
  reg  cpu2tt_r2;
  wire cpu2tt_pulse = cpu2tt_r2 ^ cpu2tt_r1;
  //---
  always @(posedge wb_clk) begin
    if (wb_rst) begin
      cpu2tt_r2 <= 1'b0;
      cpu2tt_r1 <= 1'b0;
    end
    else begin
      cpu2tt_r2 <= cpu2tt_r1;
      cpu2tt_r1 <= spr_bus_toggle_i;
    end
  end // at wb-clock

  // SPR's STB & ACK in Wishbone clock domain
  reg   spr_tt_stb_r;
  wire  spr_tt_ack;
  // ---
  always @(posedge wb_clk) begin
    if (wb_rst)
      spr_tt_stb_r <= 1'b0;
    else if (spr_tt_ack)
      spr_tt_stb_r <= 1'b0;
    else if (cpu2tt_pulse)
      spr_tt_stb_r <= spr_bus_stb_r1;
  end // at cb-clock

  // Chip selects
  wire spr_tt_cs = spr_tt_stb_r & (spr_bus_addr_r1[14:11] == `OR1K_SPR_TT_BASE); // `SPR_BASE
  reg  spr_ttmr_cs_r;
  reg  spr_ttcr_cs_r;

  // SPR FSM states
  wire [3:0] SPR_TT_WAIT = 4'b0001,
             SPR_TT_WE   = 4'b0010,
             SPR_TT_RE   = 4'b0100,
             SPR_TT_ACK  = 4'b1000;

  // SPR FSM state register and particular states
  reg  [3:0] spr_tt_state;
  wire       spr_tt_we  = spr_tt_state[1];
  wire       spr_tt_re  = spr_tt_state[2];
  assign     spr_tt_ack = spr_tt_state[3];

  // SPR FSM
  always @(posedge wb_clk) begin
    if (wb_rst) begin
      spr_ttmr_cs_r <= 1'b0; // at reset
      spr_ttcr_cs_r <= 1'b0; // at reset
      spr_tt_state  <= SPR_TT_WAIT;
    end
    else begin
      // synthesis parallel_case
      case (spr_tt_state)
        // wait SPR access request
        SPR_TT_WAIT: begin
          if (spr_tt_cs) begin
            spr_ttmr_cs_r <= (`SPR_OFFSET(spr_bus_addr_r1) == `SPR_OFFSET(`OR1K_SPR_TTMR_ADDR));
            spr_ttcr_cs_r <= (`SPR_OFFSET(spr_bus_addr_r1) == `SPR_OFFSET(`OR1K_SPR_TTCR_ADDR));
            spr_tt_state  <= spr_bus_we_r1 ? SPR_TT_WE : SPR_TT_RE;
          end
        end
        // doing SPR write/read
        SPR_TT_WE,
        SPR_TT_RE: begin
          spr_ttmr_cs_r <= 1'b0;
          spr_ttcr_cs_r <= 1'b0;
          spr_tt_state  <= SPR_TT_ACK;
        end
        // make ack
        SPR_TT_ACK: begin
          spr_tt_state  <= SPR_TT_WAIT;
        end
        // default
        default: begin
        end
      endcase
    end
  end // at wb-clock

  // data for output to SPR BUS
  reg  [31:0] tt_dato_r;
  // ---
  always @(posedge wb_clk) begin
    if (spr_tt_re)
      tt_dato_r <= spr_ttmr_cs_r ? spr_ttmr :
                    (spr_ttcr_cs_r ? spr_ttcr : 32'd0);
  end // at clock


  // TT-ack-pulse -> CPU-ack-pulse
  //   As CPU clock assumed to be faster or equal to TT's one, we
  // don't use toggle here.
  reg  tt2cpu_ack_r1;
  reg  tt2cpu_ack_r2;
  wire tt2cpu_ack_pulse = (~tt2cpu_ack_r2) & tt2cpu_ack_r1;
  // ---
  always @(posedge cpu_clk) begin
    if (cpu_rst) begin
      tt2cpu_ack_r2 <= 1'b0;
      tt2cpu_ack_r1 <= 1'b0;
    end
    else begin
      tt2cpu_ack_r2 <= tt2cpu_ack_r1;
      tt2cpu_ack_r1 <= spr_tt_ack;
    end
  end

  // Re-clock output data in CPU clock domain
  reg  [31:0] tt2cpu_dato_r1;
  // ---
  always @(posedge cpu_clk) begin
    tt2cpu_dato_r1 <= tt_dato_r;
  end


  // SPR BUS: output data and ack (CPU clock domain)
  always @(posedge cpu_clk) begin
    if (cpu_rst)
      spr_bus_ack_tt_o <=  1'b0;
    else
      spr_bus_ack_tt_o <= tt2cpu_ack_pulse;
  end
  // SPR BUS: output data latch (1-clock valid)
  always @(posedge cpu_clk) begin
    if (tt2cpu_ack_pulse)
      spr_bus_dat_tt_o <= tt2cpu_dato_r1;
    else
      spr_bus_dat_tt_o <= 32'd0;
  end


  // TT-interrupt-level -> CPU-interrupt-level
  // Re-clock TT -> CPU interrupt
  reg  tt_rdy_r1;
  // ---
  always @(posedge cpu_clk) begin
    tt_rdy_r1 <= spr_ttmr[28];
  end
  // ---
  always @(posedge cpu_clk) begin
    if (cpu_rst)
      tt_rdy_o <= 1'b0;      
    else
      tt_rdy_o <= tt_rdy_r1 & (~spr_bus_ack_tt_o);
  end



  //-------------//
  // Timer logic //
  //-------------//

  wire ttcr_match = (spr_ttcr[27:0] == spr_ttmr[27:0]);

  // Timer SPR control
  always @(posedge wb_clk) begin
    if (wb_rst)
      spr_ttmr <= 32'd0;
    else if (spr_ttmr_cs_r & spr_tt_we)
      spr_ttmr <= spr_bus_dat_r1;
    else if (ttcr_match & spr_ttmr[29])
      spr_ttmr[28] <= 1'b1; // Generate interrupt
  end

  // Modes (spr_ttmr[31:30]):
  // 00 Tick timer is disabled.
  // 01 Timer is restarted on ttcr_match.
  // 10 Timer stops when ttcr_match is true.
  // 11 Timer does not stop when ttcr_match is true
  wire ttcr_clear = ((spr_ttmr[31:30] == 2'b01) &  ttcr_match);
  wire ttcr_run   = ((spr_ttmr[31:30] != 2'b00) & ~ttcr_match) |
                     (spr_ttmr[31:30] == 2'b11);

  always @(posedge wb_clk) begin
    if (wb_rst)
      spr_ttcr <= 32'd0;
    else if (spr_ttcr_cs_r & spr_tt_we)
      spr_ttcr <= spr_bus_dat_r1;
    else if (ttcr_clear)
      spr_ttcr <= 32'd0;
    else if (ttcr_run)
      spr_ttcr <= spr_ttcr + 1'b1;
  end

endmodule // mor1kx_ticktimer_marocchino
