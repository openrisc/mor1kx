/* ****************************************************************************
  This Source Code Form is subject to the terms of the
  Open Hardware Description License, v. 1.0. If a copy
  of the OHDL was not distributed with this file, You
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: mor1kx PIC

  Copyright (C) 2012 Authors

  Author(s): Julius Baxter <juliusbaxter@gmail.com>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_pic
  (/*AUTOARG*/
   // Outputs
   spr_picmr_o, spr_picsr_o, spr_bus_ack, spr_dat_o,
   // Inputs
   clk, rst, irq_i, spr_we_i, spr_addr_i, spr_dat_i
   );

   parameter OPTION_PIC_TRIGGER="EDGE";

   input clk;
   input rst;

   input [31:0] irq_i;
   
   output [31:0] spr_picmr_o;
   output [31:0] spr_picsr_o;

   // SPR Bus interface
   input 	 spr_we_i;
   input [15:0]  spr_addr_i;
   input [31:0]  spr_dat_i;
   output 	 spr_bus_ack;
   output [31:0] spr_dat_o;

   // Registers
   reg [31:0] 	 spr_picmr;
   reg [31:0] 	 spr_picsr;

   wire [31:0] 	 irq_unmasked;

   assign spr_picmr_o = spr_picmr;
   assign spr_picsr_o = spr_picsr;

   assign spr_bus_ack = 1'b1;
   assign spr_dat_o =  (spr_addr_i==`OR1K_SPR_PICSR_ADDR) ?
		       spr_picsr :
		       (spr_addr_i==`OR1K_SPR_PICMR_ADDR) ?
		       spr_picmr : 0;

   assign irq_unmasked = spr_picmr & irq_i;

   generate
      
      genvar 	 irqline;

      if (OPTION_PIC_TRIGGER=="EDGE") begin : edge_triggered
	 for(irqline=0;irqline<32;irqline=irqline+1)
	   begin: picgenerate
	      // PIC status register
	      always @(posedge clk `OR_ASYNC_RST)
		if (rst)
		  spr_picsr[irqline] <= 0;
	      // Clear
		else if (spr_we_i & spr_addr_i==`OR1K_SPR_PICSR_ADDR)
		  spr_picsr[irqline] <= spr_dat_i[irqline] ?
					       spr_picsr[irqline] : 0;
	      // Set
		else if (!spr_picsr[irqline] & irq_unmasked[irqline])
		  spr_picsr[irqline] <= 1;
	   end // block: picgenerate
      end // if (OPTION_PIC_TRIGGER=="EDGE")

      else if (OPTION_PIC_TRIGGER=="LEVEL") begin : level_triggered
	 for(irqline=0;irqline<32;irqline=irqline+1)
	   begin: picsrlevelgenerate
	      // PIC status register
	      always @(posedge clk `OR_ASYNC_RST)
		spr_picsr[irqline] <= irq_unmasked[irqline];
	   end
      end // if (OPTION_PIC_TRIGGER=="LEVEL")

      else if (OPTION_PIC_TRIGGER=="LATCHED_LEVEL") begin : latched_level
	 for(irqline=0;irqline<32;irqline=irqline+1)
	   begin: piclatchedlevelgenerate
	      // PIC status register
	      always @(posedge clk `OR_ASYNC_RST)
		if (rst)
		  spr_picsr[irqline] <= 0;
		else if (spr_we_i & spr_addr_i==`OR1K_SPR_PICSR_ADDR)
		  spr_picsr[irqline] <= irq_unmasked[irqline] |
					       spr_dat_i[irqline];
		else
		  spr_picsr[irqline] <= spr_picsr[irqline] |
					irq_unmasked[irqline];
	   end // block: picgenerate
      end // if (OPTION_PIC_TRIGGER=="EDGE")

      else begin : invalid
	 initial begin
	    $display("Error - invalid PIC level detection option %s",
		     OPTION_PIC_TRIGGER);
	    $finish;
	 end
      end // else: !if(OPTION_PIC_TRIGGER=="LEVEL")
   endgenerate

   // PIC (un)mask register
   // Bottom two IRQs permanently unmasked
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_picmr <= {30'd0, 2'b11};
     else if (spr_we_i & spr_addr_i==`OR1K_SPR_PICMR_ADDR)
       spr_picmr <= {spr_dat_i[31:2], 2'b11};

endmodule // mor1kx_pic


