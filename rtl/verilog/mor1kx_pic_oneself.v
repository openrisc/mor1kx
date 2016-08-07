////////////////////////////////////////////////////////////////////////
//                                                                    //
//  mor1kx_pic_oneself                                                //
//                                                                    //
//  Description: Programmable Interrupt Controller for OR1K           //
//               Re-factored version of Julius Baxter's mor1kx PIC    //
//               The version is decoupled of CTRL and initially       //
//               was designed for MAROCCHINO pipeline                 //
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

module mor1kx_pic_oneself
#(
  parameter OPTION_PIC_TRIGGER    = "LEVEL",
  parameter OPTION_PIC_NMI_WIDTH  = 0
 )
(
  // clock and reset
  input             clk,
  input             rst,
  // input interrupt lines
  input      [31:0] irq_i,
  // output interrupt lines
  output     [31:0] spr_picsr_o,
  // SPR BUS
  //  # inputs
  input      [15:0] spr_bus_addr_i,
  input             spr_bus_we_i,
  input             spr_bus_stb_i,
  input      [31:0] spr_bus_dat_i,
  //  # outputs
  output reg [31:0] spr_bus_dat_pic_o,
  output reg        spr_bus_ack_pic_o
);

  // Registers
  reg [31:0] spr_picmr;
  reg [31:0] spr_picsr;


  // SPR BUS interface
  wire spr_pic_cs = spr_bus_stb_i & (`SPR_BASE(spr_bus_addr_i) == `OR1K_SPR_PIC_BASE);
  wire spr_pic_we = spr_pic_cs &  spr_bus_we_i;
  wire spr_pic_re = spr_pic_cs & ~spr_bus_we_i;

  wire spr_picmr_cs = (`SPR_OFFSET(spr_bus_addr_i) == `SPR_OFFSET(`OR1K_SPR_PICMR_ADDR));
  wire spr_picsr_cs = (`SPR_OFFSET(spr_bus_addr_i) == `SPR_OFFSET(`OR1K_SPR_PICSR_ADDR));

  reg spr_pic_wr_r;

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      spr_pic_wr_r      <= 1'b0;
      spr_bus_ack_pic_o <= 1'b0;
      spr_bus_dat_pic_o <= 32'd0;
    end
    else if (spr_bus_ack_pic_o) begin // end of cycle
      spr_pic_wr_r      <= 1'b0;
      spr_bus_ack_pic_o <= 1'b0;
      spr_bus_dat_pic_o <= 32'd0;
    end
    else begin
      if (spr_pic_we) begin
        spr_pic_wr_r      <= 1'b1;
        spr_bus_ack_pic_o <= 1'b1;
        spr_bus_dat_pic_o <= 32'd0;
      end
      else if (spr_pic_re) begin
        spr_pic_wr_r      <= 1'b0;
        spr_bus_ack_pic_o <= 1'b1;
        spr_bus_dat_pic_o <= spr_picmr_cs ? spr_picmr :
                             spr_picsr_cs ? spr_picsr :
                                            32'd0;
      end
    end
  end // at clock


  assign spr_picsr_o = spr_picsr;

  wire [31:0] irq_unmasked = spr_picmr & irq_i;


  generate

  genvar  irqline;

  if (OPTION_PIC_TRIGGER == "EDGE") begin : edge_triggered
    reg  [31:0] irq_unmasked_r;
    wire [31:0] irq_unmasked_edge;

    always @(posedge clk `OR_ASYNC_RST)
      if (rst)
        irq_unmasked_r <= 32'd0;
      else
        irq_unmasked_r <= irq_unmasked;

    for(irqline=0; irqline<32; irqline=irqline+1)  begin : picgenerate
      assign irq_unmasked_edge[irqline] = irq_unmasked[irqline] &
                                           ~irq_unmasked_r[irqline];

      // PIC status register
      always @(posedge clk `OR_ASYNC_RST)
        if (rst)
          spr_picsr[irqline] <= 1'b0;
        // Set
        else if (irq_unmasked_edge[irqline])
          spr_picsr[irqline] <= 1'b1;
        // Clear
        else if (spr_pic_wr_r & spr_picsr_cs & spr_bus_dat_i[irqline])
          spr_picsr[irqline] <= 1'b0;
    end
  end // trigger is "edge"

  else if (OPTION_PIC_TRIGGER == "LEVEL") begin : level_triggered
    for(irqline=0; irqline<32; irqline=irqline+1) begin : picsrlevelgenerate
      // PIC status register
      always @(*)
        spr_picsr[irqline] <= irq_unmasked[irqline];
    end
  end // trigger is "level"

  else if (OPTION_PIC_TRIGGER == "LATCHED_LEVEL") begin : latched_level
    for(irqline=0; irqline<32; irqline=irqline+1) begin : piclatchedlevelgenerate
      // PIC status register
      always @(posedge clk `OR_ASYNC_RST)
        if (rst)
          spr_picsr[irqline] <= 1'b0;
        else if (spr_pic_wr_r & spr_picsr_cs)
          spr_picsr[irqline] <= irq_unmasked[irqline] | spr_bus_dat_i[irqline];
        else
          spr_picsr[irqline] <= spr_picsr[irqline] | irq_unmasked[irqline];
    end // block: picgenerate
  end // trigger is "latched level"

  else begin : invalid
    initial begin
      $display("Error - invalid PIC level detection option %s",
                OPTION_PIC_TRIGGER);
      $finish;
    end
  end  // trigger switcher

  endgenerate

  // PIC (un)mask register
  always @(posedge clk `OR_ASYNC_RST)
    if (rst)
      spr_picmr <= {{(32-OPTION_PIC_NMI_WIDTH){1'b0}},
                    {OPTION_PIC_NMI_WIDTH{1'b1}}};
    else if (spr_pic_wr_r & spr_picmr_cs)
      spr_picmr <= {spr_bus_dat_i[31:OPTION_PIC_NMI_WIDTH],
                    {OPTION_PIC_NMI_WIDTH{1'b1}}};

endmodule // mor1kx_pic_oneself
