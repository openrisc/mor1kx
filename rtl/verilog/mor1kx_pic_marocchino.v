////////////////////////////////////////////////////////////////////////
//                                                                    //
//  mor1kx_pic_marocchino                                             //
//                                                                    //
//  Description:                                                      //
//  Programmable Interrupt Controller for OR1K                        //
//    (a) Re-factored version of Julius Baxter's mor1kx PIC           //
//    (b) Decoupled of CTRL module                                    //
//    (c) PIC itself is in Wishbone clock domain wile SPR bus is in   //
//        CPU clock domain                                            //
//    (d) Actually, CDC is not implemented completely yet.            //
//        The CPU clock could be greater or equal to Wishbone one,    //
//        buth them must be aligned. So, synchronizers consist of     //
//        single latch named "*_r2". To implement full synchronizers  //
//        latches *_r1 shuld be appropriatelly added.                 //
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

module mor1kx_pic_marocchino
#(
  parameter OPTION_PIC_TRIGGER    = "LEVEL",
  parameter OPTION_PIC_NMI_WIDTH  = 0
 )
(
  // Wishbone side clock and reset
  input             wb_clk,
  input             wb_rst,
  // CPU side clock and reset
  input             cpu_clk,
  input             cpu_rst,
  // input interrupt lines
  input      [31:0] irq_i,
  // output interrupt lines
  output reg        pic_rdy_o, // an interrupt
  // SPR BUS
  //  # inputs
  input      [15:0] spr_bus_addr_i,
  input             spr_bus_we_i,
  input             spr_bus_stb_i,
  input             spr_bus_toggle_i,
  input      [31:0] spr_bus_dat_i,
  //  # outputs
  output reg [31:0] spr_bus_dat_pic_o,
  output reg        spr_bus_ack_pic_o
);

  // PIC Registers
  reg [31:0] spr_picmr;
  reg [31:0] spr_picsr;


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
  reg  cpu2pic_r1;
  reg  cpu2pic_r2;
  wire cpu2pic_pulse = cpu2pic_r2 ^ cpu2pic_r1;
  //---
  always @(posedge wb_clk) begin
    if (wb_rst) begin
      cpu2pic_r2 <= 1'b0;
      cpu2pic_r1 <= 1'b0;
    end
    else begin
      cpu2pic_r2 <= cpu2pic_r1;
      cpu2pic_r1 <= spr_bus_toggle_i;
    end
  end // at wb-clock

  // SPR's STB & ACK in Wishbone clock domain
  reg   spr_pic_stb_r;
  wire  spr_pic_ack;
  // ---
  always @(posedge wb_clk) begin
    if (wb_rst)
      spr_pic_stb_r <= 1'b0;
    else if (spr_pic_ack)
      spr_pic_stb_r <= 1'b0;
    else if (cpu2pic_pulse)
      spr_pic_stb_r <= spr_bus_stb_r1;
  end // at cb-clock

  // Chip selects
  wire spr_pic_cs = spr_pic_stb_r & (spr_bus_addr_r1[14:11] == `OR1K_SPR_PIC_BASE); // `SPR_BASE
  reg  spr_picmr_cs_r;
  reg  spr_picsr_cs_r;

  // SPR FSM states
  wire [3:0] SPR_PIC_WAIT = 4'b0001,
             SPR_PIC_WE   = 4'b0010,
             SPR_PIC_RE   = 4'b0100,
             SPR_PIC_ACK  = 4'b1000;

  // SPR FSM state register and particular states
  reg  [3:0] spr_pic_state;
  wire       spr_pic_we  = spr_pic_state[1];
  wire       spr_pic_re  = spr_pic_state[2];
  assign     spr_pic_ack = spr_pic_state[3];

  // SPR FSM
  always @(posedge wb_clk) begin
    if (wb_rst) begin
      spr_picmr_cs_r <= 1'b0; // at reset
      spr_picsr_cs_r <= 1'b0; // at reset
      spr_pic_state  <= SPR_PIC_WAIT;
    end
    else begin
      // synthesis parallel_case
      case (spr_pic_state)
        // wait SPR access request
        SPR_PIC_WAIT: begin
          if (spr_pic_cs) begin
            spr_picmr_cs_r <= (`SPR_OFFSET(spr_bus_addr_r1) == `SPR_OFFSET(`OR1K_SPR_PICMR_ADDR));
            spr_picsr_cs_r <= (`SPR_OFFSET(spr_bus_addr_r1) == `SPR_OFFSET(`OR1K_SPR_PICSR_ADDR));
            spr_pic_state  <= spr_bus_we_r1 ? SPR_PIC_WE : SPR_PIC_RE;
          end
        end
        // doing SPR write/read
        SPR_PIC_WE,
        SPR_PIC_RE: begin
          spr_picmr_cs_r <= 1'b0;
          spr_picsr_cs_r <= 1'b0;
          spr_pic_state  <= SPR_PIC_ACK;
        end
        // make ack
        SPR_PIC_ACK: begin
          spr_pic_state  <= SPR_PIC_WAIT;
        end
        // default
        default: begin
        end
      endcase
    end
  end // at wb-clock

  // data for output to SPR BUS
  reg  [31:0] pic_dato_r;
  // ---
  always @(posedge wb_clk) begin
    if (spr_pic_re)
      pic_dato_r <= spr_picmr_cs_r ? spr_picmr :
                     (spr_picsr_cs_r ? spr_picsr : 32'd0);
  end // at clock


  // PIC-ack-pulse -> CPU-ack-pulse
  //   As CPU clock assumed to be faster or equal to PIC's one, we
  // don't use toggle here.
  reg  pic2cpu_ack_r1;
  reg  pic2cpu_ack_r2;
  wire pic2cpu_ack_pulse = (~pic2cpu_ack_r2) & pic2cpu_ack_r1;
  // ---
  always @(posedge cpu_clk) begin
    if (cpu_rst) begin
      pic2cpu_ack_r2 <= 1'b0;
      pic2cpu_ack_r1 <= 1'b0;
    end
    else begin
      pic2cpu_ack_r2 <= pic2cpu_ack_r1;
      pic2cpu_ack_r1 <= spr_pic_ack;
    end
  end

  // Re-clock output data in CPU clock domain
  reg  [31:0] pic2cpu_dato_r1;
  // ---
  always @(posedge cpu_clk) begin
    pic2cpu_dato_r1 <= pic_dato_r;
  end

  // SPR BUS: ACK (CPU clock domain, 1-clock)
  always @(posedge cpu_clk) begin
    if (cpu_rst)
      spr_bus_ack_pic_o <= 1'b0;
    else
      spr_bus_ack_pic_o <= pic2cpu_ack_pulse;
  end
  // SPR BUS: output data (CPU clock domain, valid for 1-clock)
  always @(posedge cpu_clk) begin
    if (pic2cpu_ack_pulse)
      spr_bus_dat_pic_o <= pic2cpu_dato_r1;
    else
      spr_bus_dat_pic_o <= 32'd0;
  end


  // Re-clock PIC -> CPU interrupts
  reg  [31:0] spr_picsr_r1;
  // ---
  always @(posedge cpu_clk) begin
    spr_picsr_r1 <= spr_picsr;
  end
  // ---
  always @(posedge cpu_clk) begin
    if (cpu_rst)
      pic_rdy_o <= 1'b0;
    else
      pic_rdy_o <= (|spr_picsr_r1);
  end


  //-----------//
  // PIC logic //
  //-----------//

  // not masked IRQs
  wire [31:0] irq_unmasked = spr_picmr & irq_i;

  // new mask by SPR set
  wire [31:0] spr_pic_mask = {spr_bus_dat_r1[31:OPTION_PIC_NMI_WIDTH],
                              {OPTION_PIC_NMI_WIDTH{1'b1}}};

  // PIC (un)mask register
  always @(posedge wb_clk) begin
    if (wb_rst)
      spr_picmr <= {{(32-OPTION_PIC_NMI_WIDTH){1'b0}},
                    {OPTION_PIC_NMI_WIDTH{1'b1}}};
    else if (spr_picmr_cs_r & spr_pic_we)
      spr_picmr <= spr_pic_mask;
  end

  // PIC status register
  generate
  genvar  irqline;
  /* verilator lint_off WIDTH */
  if (OPTION_PIC_TRIGGER == "EDGE") begin : edge_triggered
  /* verilator lint_on WIDTH */

    reg  [31:0] irq_unmasked_r;
    wire [31:0] irq_unmasked_edge;

    always @(posedge wb_clk) begin
      if (wb_rst)
        irq_unmasked_r <= 32'd0;
      else
        irq_unmasked_r <= irq_unmasked;
    end

    for(irqline=0; irqline<32; irqline=irqline+1)  begin : picgenerate
      assign irq_unmasked_edge[irqline] = irq_unmasked[irqline] &
                                           ~irq_unmasked_r[irqline];

      // PIC status register
      always @(posedge wb_clk) begin
        if (wb_rst)
          spr_picsr[irqline] <= 1'b0;
        // Set
        else if (irq_unmasked_edge[irqline])
          spr_picsr[irqline] <= 1'b1;
        // Clear
        else if (spr_picsr_cs_r & spr_pic_we & spr_bus_addr_r1[irqline])
          spr_picsr[irqline] <= 1'b0;
      end
    end

  end // trigger is "edge"
  /* verilator lint_off WIDTH */
  else if (OPTION_PIC_TRIGGER == "LEVEL") begin : level_triggered
  /* verilator lint_on WIDTH */

    always @(irq_unmasked) begin
      spr_picsr = irq_unmasked;
    end

  end // trigger is "level"
  /* verilator lint_off WIDTH */
  else if (OPTION_PIC_TRIGGER == "LATCHED_LEVEL") begin : latched_level
  /* verilator lint_on WIDTH */

    always @(posedge wb_clk) begin
      if (wb_rst)
        spr_picsr <= 32'd0;
      else if (spr_picmr_cs_r & spr_pic_we)
        spr_picsr <= spr_pic_mask & spr_picsr;
      else if (spr_picsr_cs_r & spr_pic_we)
        spr_picsr <= irq_unmasked | spr_bus_addr_r1;
      else
        spr_picsr <= irq_unmasked | spr_picsr;
    end

  end // trigger is "latched level"
  else begin : invalid

    initial begin
      $display("Error - invalid PIC level detection option %s",
                OPTION_PIC_TRIGGER);
      $finish;
    end

  end  // trigger switcher
  endgenerate

endmodule // mor1kx_pic_marocchino
