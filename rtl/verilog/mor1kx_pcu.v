/* ****************************************************************************
  This Source Code Form is subject to the terms of the
  Open Hardware Description License, v. 1.0. If a copy
  of the OHDL was not distributed with this file, You
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: mor1kx Perfomance Counters Unit

  Copyright (C) 2016 Authors

  Author(s): Alexey Baturo <baturo.alexey@gmail.com>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_pcu
  (/*AUTOARG*/
   // Outputs
   spr_picmr_o, spr_picsr_o, spr_bus_ack, spr_dat_o,
   // Inputs
   clk, rst, irq_i, spr_access_i, spr_we_i, spr_addr_i, spr_dat_i
   );

   parameter OPTION_PIC_TRIGGER="LEVEL";
   parameter OPTION_PIC_NMI_WIDTH = 0;

   input clk;
   input rst;

   input [31:0] irq_i;

   output [31:0] spr_picmr_o;
   output [31:0] spr_picsr_o;

   // SPR Bus interface
   input         spr_access_i;
   input         spr_we_i;
   input [15:0]  spr_addr_i;
   input [31:0]  spr_dat_i;
   output        spr_bus_ack;
   output [31:0] spr_dat_o;

   // Registers
   reg [31:0]    spr_picmr;
   reg [31:0]    spr_picsr;

   wire spr_picmr_access;
   wire spr_picsr_access;

   wire [31:0]   irq_unmasked;

   assign spr_picmr_o = spr_picmr;
   assign spr_picsr_o = spr_picsr;

   assign spr_picmr_access =
     spr_access_i &
     (`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_PICMR_ADDR));
   assign spr_picsr_access =
     spr_access_i &
     (`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_PICSR_ADDR));

   assign spr_bus_ack = spr_access_i;
   assign spr_dat_o =  (spr_access_i & spr_picsr_access) ? spr_picsr :
                       (spr_access_i & spr_picmr_access) ? spr_picmr :
                       0;

   assign irq_unmasked = spr_picmr & irq_i;

   generate

      genvar 	 irqline;

      if (OPTION_PIC_TRIGGER=="EDGE") begin : edge_triggered
         reg [31:0] irq_unmasked_r;
         wire [31:0] irq_unmasked_edge;

         always @(posedge clk `OR_ASYNC_RST)
           if (rst)
             irq_unmasked_r <= 0;
           else
             irq_unmasked_r <= irq_unmasked;

         for(irqline=0;irqline<32;irqline=irqline+1)  begin: picgenerate
            assign irq_unmasked_edge[irqline] = irq_unmasked[irqline] &
                                                !irq_unmasked_r[irqline];

            // PIC status register
            always @(posedge clk `OR_ASYNC_RST)
              if (rst)
                spr_picsr[irqline] <= 0;
              // Set
              else if (irq_unmasked_edge[irqline])
                spr_picsr[irqline] <= 1;
              // Clear
              else if (spr_we_i & spr_picsr_access & spr_dat_i[irqline])
                spr_picsr[irqline] <= 0;
         end
      end else if (OPTION_PIC_TRIGGER=="LEVEL") begin : level_triggered
         for(irqline=0;irqline<32;irqline=irqline+1)
           begin: picsrlevelgenerate
              // PIC status register
              always @(*)
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
		else if (spr_we_i && spr_picsr_access)
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
   always @(posedge clk `OR_ASYNC_RST)
     if (rst)
       spr_picmr <= {{(32-OPTION_PIC_NMI_WIDTH){1'b0}},
		     {OPTION_PIC_NMI_WIDTH{1'b1}}};
     else if (spr_we_i && spr_picmr_access)
       spr_picmr <= {spr_dat_i[31:OPTION_PIC_NMI_WIDTH],
		     {OPTION_PIC_NMI_WIDTH{1'b1}}};

endmodule // mor1kx_pcu
