/* ****************************************************************************
  This Source Code Form is subject to the terms of the 
  Open Hardware Description License, v. 1.0. If a copy 
  of the OHDL was not distributed with this file, You 
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: mor1kx SPRs indicating configuration and version
                                                  
  All registers are read only and configured at synthesis time.
 
  Note that the outputs do not have the usual "_o" prefix on the port names
  as this module is intended to be instantiated without a Verilog-mode
  AUTO_TEMPLATE, and as the module is providing read-only signals, there's
  no confusion about the direction of the ports.
 
  Copyright (C) 2012 Authors
 
  Author(s): Julius Baxter <juliusbaxter@gmail.com>
 
***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_cfgrs
  (/*AUTOARG*/
   // Outputs
   spr_vr, spr_upr, spr_cpucfgr, spr_dmmucfgr, spr_immucfgr,
   spr_dccfgr, spr_iccfgr, spr_dcfgr, spr_pccfgr, spr_fpcsr
   );
   
   parameter FEATURE_SYSCALL            = "ENABLED";
   parameter FEATURE_TRAP               = "ENABLED";
   parameter FEATURE_RANGE              = "ENABLED";

   parameter FEATURE_DATACACHE          = "NONE";
   parameter OPTION_DCACHE_BLOCK_WIDTH  = 5;
   parameter OPTION_DCACHE_SET_WIDTH    = 9;
   parameter OPTION_DCACHE_WAYS         = 2;
   parameter FEATURE_DMMU               = "NONE";
   parameter FEATURE_INSTRUCTIONCACHE   = "NONE";
   parameter OPTION_ICACHE_BLOCK_WIDTH  = 5;
   parameter OPTION_ICACHE_SET_WIDTH    = 9;
   parameter OPTION_ICACHE_WAYS         = 2;
   parameter FEATURE_IMMU               = "NONE";
   parameter FEATURE_PIC                = "ENABLED";
   parameter FEATURE_TIMER              = "ENABLED";
   parameter FEATURE_DEBUGUNIT          = "NONE";
   parameter FEATURE_PERFCOUNTERS       = "NONE";
   parameter FEATURE_PMU                = "NONE";
   parameter FEATURE_MAC                = "NONE";
   parameter FEATURE_FPU                = "NONE";   

   parameter OPTION_PIC_TRIGGER         = "EDGE";

   parameter FEATURE_DSX                = "NONE";
   parameter FEATURE_FASTCONTEXTS       = "NONE";
   parameter FEATURE_OVERFLOW           = "NONE";

   output [31:0] spr_vr;
   output [31:0] spr_upr;
   output [31:0] spr_cpucfgr;
   output [31:0] spr_dmmucfgr;
   output [31:0] spr_immucfgr;
   output [31:0] spr_dccfgr;
   output [31:0] spr_iccfgr;
   output [31:0] spr_dcfgr;
   output [31:0] spr_pccfgr;
   output [31:0] spr_fpcsr;

   assign spr_vr[`OR1K_SPR_VR_REV] = 0;
   assign spr_vr[`OR1K_SPR_VR_RESERVED] = 0;
   assign spr_vr[`OR1K_SPR_VR_CFG] = 0;
   assign spr_vr[`OR1K_SPR_VR_VER] = 0;
   
   assign spr_upr[`OR1K_SPR_UPR_UP] = 1;
   assign spr_upr[`OR1K_SPR_UPR_DCP] = (FEATURE_DATACACHE!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_ICP] = (FEATURE_INSTRUCTIONCACHE!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_DMP] = (FEATURE_DMMU!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_IMP] = (FEATURE_IMMU!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_MP] = (FEATURE_MAC!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_DUP] = (FEATURE_DEBUGUNIT!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_PCUP] = (FEATURE_PERFCOUNTERS!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_PICP] = (FEATURE_PIC!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_PMP] = (FEATURE_PMU!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_TTP] = (FEATURE_TIMER!="NONE");
   assign spr_upr[`OR1K_SPR_UPR_RESERVED] = 0;
   assign spr_upr[`OR1K_SPR_UPR_CUP] = 0;

   assign spr_cpucfgr[`OR1K_SPR_CPUCFGR_NSGF] = 0;
   assign spr_cpucfgr[`OR1K_SPR_CPUCFGR_CFG] = 0;
   assign spr_cpucfgr[`OR1K_SPR_CPUCFGR_OB32S] = 1;
   assign spr_cpucfgr[`OR1K_SPR_CPUCFGR_OB64S] = 0;
   assign spr_cpucfgr[`OR1K_SPR_CPUCFGR_OF32S] = 0;
   assign spr_cpucfgr[`OR1K_SPR_CPUCFGR_OF64S] = 0;
   assign spr_cpucfgr[`OR1K_SPR_CPUCFGR_OV64S] = 0;
   assign spr_cpucfgr[`OR1K_SPR_CPUCFGR_RESERVED] = 0;

   assign spr_dmmucfgr = 0;
   assign spr_immucfgr = 0;

   /* Data Cache Configuration register */
   /* Reserved */
   assign spr_dccfgr[31:15] = 0;
   /* Cache Block Write-Back Register Implemented */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_CBWBRI] = 0;
   /* Cache Block Flush Register Implemented */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_CBFRI] = (FEATURE_DATACACHE!="NONE");
   /* Cache Block Lock Register Implemented */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_CBLRI] = 0;
   /* Cache Block Prefetch Register Implemented */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_CBPRI] = 0;
   /* Cache Block Invalidate Register Implemented */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_CBIRI] = (FEATURE_DATACACHE!="NONE");
   /* Cache Control Register Implemented */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_CCRI] = 0;
   /* Cache Write Strategy (0 = write-through, 1 = write-back) */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_CWS] = 0;
   /* Cache Block Size (0 = 16 bytes, 1 = 32 bytes) */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_CBS] = (FEATURE_DATACACHE!="NONE") ?
                                             (OPTION_DCACHE_BLOCK_WIDTH == 5 ? 1 : 0) :  0;
  /* Number of Cache Sets */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_NCS] = (FEATURE_DATACACHE!="NONE") ?
                                             OPTION_DCACHE_SET_WIDTH : 0;
   /* Number of Cache Ways */
   assign spr_dccfgr[`OR1K_SPR_DCCFGR_NCW] = (FEATURE_DATACACHE!="NONE") ?
                                             (OPTION_DCACHE_WAYS == 1) ? 3'd0 :
                                             (OPTION_DCACHE_WAYS == 2) ? 3'd1 :
                                             (OPTION_DCACHE_WAYS == 4) ? 3'd2 :
                                             (OPTION_DCACHE_WAYS == 8) ? 3'd3 :
                                             (OPTION_DCACHE_WAYS == 16) ? 3'd4 :
                                             (OPTION_DCACHE_WAYS == 32) ? 3'd5 :
                                             3'd0 : 3'd0;

   /* Instruction Cache Configuration register */
   /* Reserved */
   assign spr_iccfgr[31:13] = 0;
   assign spr_iccfgr[8] = 0;
   /* Cache Block Lock Register Implemented */
   assign spr_iccfgr[`OR1K_SPR_ICCFGR_CBLRI] = 0;
   /* Cache Block Prefetch Register Implemented */
   assign spr_iccfgr[`OR1K_SPR_ICCFGR_CBPRI] = 0;
   /* Cache Block Invalidate Register Implemented */
   assign spr_iccfgr[`OR1K_SPR_ICCFGR_CBIRI] = (FEATURE_INSTRUCTIONCACHE!="NONE");
   /* Cache Control Register Implemented */
   assign spr_iccfgr[`OR1K_SPR_ICCFGR_CCRI] = 0;
   /* Cache Block Size (0 = 16 bytes, 1 = 32 bytes) */
   assign spr_iccfgr[`OR1K_SPR_ICCFGR_CBS] = (FEATURE_INSTRUCTIONCACHE!="NONE") ?
                                             (OPTION_ICACHE_BLOCK_WIDTH == 5 ? 1 : 0) :  0;
  /* Number of Cache Sets */
   assign spr_iccfgr[`OR1K_SPR_ICCFGR_NCS] = (FEATURE_INSTRUCTIONCACHE!="NONE") ?
                                             OPTION_ICACHE_SET_WIDTH : 0;
   /* Number of Cache Ways */
   assign spr_iccfgr[`OR1K_SPR_ICCFGR_NCW] = (FEATURE_INSTRUCTIONCACHE!="NONE") ?
                                             (OPTION_ICACHE_WAYS == 1) ? 3'd0 :
                                             (OPTION_ICACHE_WAYS == 2) ? 3'd1 :
                                             (OPTION_ICACHE_WAYS == 4) ? 3'd2 :
                                             (OPTION_ICACHE_WAYS == 8) ? 3'd3 :
                                             (OPTION_ICACHE_WAYS == 16) ? 3'd4 :
                                             (OPTION_ICACHE_WAYS == 32) ? 3'd5 :
                                             3'd0 : 3'd0;
   

   assign spr_dcfgr = 0;
   assign spr_pccfgr = 0;   
   assign spr_fpcsr = 0;


endmodule // mor1kx_cfgrs
