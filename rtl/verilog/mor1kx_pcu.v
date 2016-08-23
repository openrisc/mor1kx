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
   spr_bus_ack, spr_dat_o,
   // Inputs
   clk, rst, spr_access_i, spr_we_i, spr_addr_i, spr_dat_i, spr_re_i,
   pcu_event_load_i, pcu_event_store_i, pcu_event_ifetch_i,
   pcu_event_dcache_miss_i, pcu_event_icache_miss_i,
   pcu_event_ifetch_stall_i, pcu_event_lsu_stall_i,
   pcu_event_brn_stall_i, pcu_event_dtlb_miss_i, pcu_event_itlb_miss_i,
   pcu_event_datadep_stall_i,
   spr_sys_mode_i
   );

   parameter OPTION_PCU_NUM = 8;

   input clk;
   input rst;

   // SPR Bus interface
   input         spr_access_i;
   input         spr_we_i;
   input         spr_re_i;
   input [15:0]  spr_addr_i;
   input [31:0]  spr_dat_i;
   output        spr_bus_ack;
   output [31:0] spr_dat_o;

   // Current cpu mode: user/supervisor
   input         spr_sys_mode_i;
   // Events that can occur
   input         pcu_event_load_i;
   input         pcu_event_store_i;
   input         pcu_event_ifetch_i;
   input         pcu_event_dcache_miss_i;
   input         pcu_event_icache_miss_i;
   input         pcu_event_ifetch_stall_i;
   input         pcu_event_lsu_stall_i;
   input         pcu_event_brn_stall_i;
   input         pcu_event_dtlb_miss_i;
   input         pcu_event_itlb_miss_i;
   input         pcu_event_datadep_stall_i;

   // Registers
   reg [31:0]    pcu_pccr[0:OPTION_PCU_NUM - 1];
   reg [31:0]    pcu_pcmr[0:OPTION_PCU_NUM - 1];

   wire pcu_pccr_access;
   wire pcu_pcmr_access;

   // check if we access pcu
   assign pcu_pccr_access =
     spr_access_i &
     ((`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_PCCR0_ADDR)) |
      (`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_PCCR1_ADDR)) |
      (`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_PCCR2_ADDR)) |
      (`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_PCCR3_ADDR)) |
      (`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_PCCR4_ADDR)) |
      (`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_PCCR5_ADDR)) |
      (`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_PCCR6_ADDR)) |
      (`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_PCCR7_ADDR)));

   assign pcu_pcmr_access =
     spr_access_i &
     ((`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_PCMR0_ADDR)) |
      (`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_PCMR1_ADDR)) |
      (`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_PCMR2_ADDR)) |
      (`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_PCMR3_ADDR)) |
      (`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_PCMR4_ADDR)) |
      (`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_PCMR5_ADDR)) |
      (`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_PCMR6_ADDR)) |
      (`SPR_OFFSET(spr_addr_i) == `SPR_OFFSET(`OR1K_SPR_PCMR7_ADDR)));

   // put data on data bus
   assign spr_bus_ack = spr_access_i;
   assign spr_dat_o   = (spr_access_i & pcu_pccr_access & spr_re_i) ? pcu_pccr[spr_addr_i[2:0]] :
                        (spr_access_i & pcu_pcmr_access & spr_re_i & spr_sys_mode_i) ? pcu_pcmr[spr_addr_i[2:0]] :
                        0;

   genvar pcu_num;
   generate
      for(pcu_num = 0; pcu_num < OPTION_PCU_NUM; pcu_num = pcu_num + 1) begin: pcu_generate
         always @(posedge clk `OR_ASYNC_RST) begin
            if (rst) begin
               pcu_pccr[pcu_num] = 32'd0;
               pcu_pcmr[pcu_num] = 32'd0 | 1 << `OR1K_PCMR_CP;
            end else begin
               if (spr_we_i) begin
                  if (spr_sys_mode_i) begin
                     if (pcu_pccr_access)
                        pcu_pccr[spr_addr_i[2:0]] <= spr_dat_i;
                     if (pcu_pcmr_access)
                        pcu_pccr[spr_addr_i[2:0]][25:1] <= spr_dat_i[25:1];
                  end else begin
                  end
               end else begin
                  if (pcu_pcmr[pcu_num][`OR1K_PCMR_WPE] & (pcu_event_load_i << `OR1K_PCMR_LA))
                     pcu_pccr[pcu_num] <= pcu_pccr[pcu_num] + 1;
                  if (pcu_pcmr[pcu_num][`OR1K_PCMR_WPE] & (pcu_event_store_i << `OR1K_PCMR_SA))
                     pcu_pccr[pcu_num] <= pcu_pccr[pcu_num] + 1;
                  if (pcu_pcmr[pcu_num][`OR1K_PCMR_WPE] & (pcu_event_ifetch_i << `OR1K_PCMR_IF))
                     pcu_pccr[pcu_num] <= pcu_pccr[pcu_num] + 1;
                  if (pcu_pcmr[pcu_num][`OR1K_PCMR_WPE] & (pcu_event_dcache_miss_i << `OR1K_PCMR_DCM))
                     pcu_pccr[pcu_num] <= pcu_pccr[pcu_num] + 1;
                  if (pcu_pcmr[pcu_num][`OR1K_PCMR_WPE] & (pcu_event_icache_miss_i << `OR1K_PCMR_ICM))
                     pcu_pccr[pcu_num] <= pcu_pccr[pcu_num] + 1;
                  if (pcu_pcmr[pcu_num][`OR1K_PCMR_WPE] & (pcu_event_ifetch_stall_i << `OR1K_PCMR_IFS))
                     pcu_pccr[pcu_num] <= pcu_pccr[pcu_num] + 1;
                  if (pcu_pcmr[pcu_num][`OR1K_PCMR_WPE] & (pcu_event_lsu_stall_i << `OR1K_PCMR_LSUS))
                     pcu_pccr[pcu_num] <= pcu_pccr[pcu_num] + 1;
                  if (pcu_pcmr[pcu_num][`OR1K_PCMR_WPE] & (pcu_event_brn_stall_i << `OR1K_PCMR_BS))
                     pcu_pccr[pcu_num] <= pcu_pccr[pcu_num] + 1;
                  if (pcu_pcmr[pcu_num][`OR1K_PCMR_WPE] & (pcu_event_dtlb_miss_i << `OR1K_PCMR_DTLBM))
                     pcu_pccr[pcu_num] <= pcu_pccr[pcu_num] + 1;
                  if (pcu_pcmr[pcu_num][`OR1K_PCMR_WPE] & (pcu_event_itlb_miss_i << `OR1K_PCMR_ITLBM))
                     pcu_pccr[pcu_num] <= pcu_pccr[pcu_num] + 1;
                  if (pcu_pcmr[pcu_num][`OR1K_PCMR_WPE] & (pcu_event_datadep_stall_i << `OR1K_PCMR_DDS))
                     pcu_pccr[pcu_num] <= pcu_pccr[pcu_num] + 1;
               end
            end
         end
      end
   endgenerate

endmodule // mor1kx_pcu
