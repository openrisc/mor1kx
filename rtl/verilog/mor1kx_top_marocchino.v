////////////////////////////////////////////////////////////////////////
//                                                                    //
//  mor1kx_top_marocchino                                             //
//                                                                    //
//  Description: Top level for stand alone mor1kx with                //
//               MAROCCHINO pipeline.                                 //
//               Based on mor1kx.v with removed AVALON bus and        //
//               use exactly mor1kx_cpu_marocchino excluding          //
//               instances of other variants of pipeline.             //
//                                                                    //
////////////////////////////////////////////////////////////////////////
//                                                                    //
//   Copyright (C) 2012 Julius Baxter                                 //
//                      juliusbaxter@gmail.com                        //
//                                                                    //
//                      Stefan Kristiansson                           //
//                      stefan.kristiansson@saunalahti.fi             //
//                                                                    //
//   Copyright (C) 2015-2019 Andrey Bacherov                          //
//                           avbacherov@opencores.org                 //
//                                                                    //
//      This Source Code Form is subject to the terms of the          //
//      Open Hardware Description License, v. 1.0. If a copy          //
//      of the OHDL was not distributed with this file, You           //
//      can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt       //
//                                                                    //
////////////////////////////////////////////////////////////////////////

`include "mor1kx-defines.v"

module mor1kx_top_marocchino
#(
  parameter OPTION_OPERAND_WIDTH        = 32,

  // temporary:
  parameter OPTION_ORFPX64A32_ABI       = "GCC5", // "GCC9" / "GCC5"

  // data cache configuration
  parameter OPTION_DCACHE_BLOCK_WIDTH   =  5,
  parameter OPTION_DCACHE_SET_WIDTH     =  9,
  parameter OPTION_DCACHE_WAYS          =  2,
  parameter OPTION_DCACHE_LIMIT_WIDTH   = 32,
  parameter OPTION_DCACHE_SNOOP         = "NONE",
  parameter OPTION_DCACHE_CLEAR_ON_INIT =  0, // !!! activate for simulation only !!!

  // data mmu
  parameter FEATURE_DMMU_HW_TLB_RELOAD  = "NONE",
  parameter OPTION_DMMU_SET_WIDTH       =  6,
  parameter OPTION_DMMU_WAYS            =  1,
  parameter OPTION_DMMU_CLEAR_ON_INIT   =  0, // !!! activate for simulation only !!!

  // store buffer
  parameter OPTION_STORE_BUFFER_DEPTH_WIDTH   = 4, // 16 taps
  parameter OPTION_STORE_BUFFER_CLEAR_ON_INIT = 0, // !!! activate for simulation only !!!

  // istruction cache
  parameter OPTION_ICACHE_BLOCK_WIDTH   =  5,
  parameter OPTION_ICACHE_SET_WIDTH     =  9,
  parameter OPTION_ICACHE_WAYS          =  2,
  parameter OPTION_ICACHE_LIMIT_WIDTH   = 32,
  parameter OPTION_ICACHE_CLEAR_ON_INIT =  0, // !!! activate for simulation only !!!

  // instruction mmu
  parameter FEATURE_IMMU_HW_TLB_RELOAD = "NONE",
  parameter OPTION_IMMU_SET_WIDTH      =  6,
  parameter OPTION_IMMU_WAYS           =  1,
  parameter OPTION_IMMU_CLEAR_ON_INIT  =  0, // !!! activate for simulation only !!!

  // Debug unit
  parameter FEATURE_DEBUGUNIT          = "NONE",
  parameter FEATURE_PERFCOUNTERS       = "NONE",

  // PIC
  parameter OPTION_PIC_TRIGGER         = "LEVEL",
  parameter OPTION_PIC_NMI_WIDTH       =  0,

  parameter OPTION_RF_CLEAR_ON_INIT    =  0, // !!! activate for simulation only !!!
  parameter OPTION_RF_ADDR_WIDTH       =  5,
  parameter OPTION_RF_WORDS            = 32,

  parameter OPTION_RESET_PC            = {{(OPTION_OPERAND_WIDTH-13){1'b0}},
                                          `OR1K_RESET_VECTOR,8'd0},

  parameter FEATURE_PSYNC              = "NONE",
  parameter FEATURE_CSYNC              = "NONE",

  parameter FEATURE_MULTICORE          = "NONE",
  parameter OPTION_RF_NUM_SHADOW_GPR   = 0,       // for multicore mostly

  parameter IBUS_WB_TYPE               = "B3_REGISTERED_FEEDBACK",
  parameter DBUS_WB_TYPE               = "B3_REGISTERED_FEEDBACK"
)
(
  // Wishbone clock and reset
  input                             wb_clk,
  input                             wb_rst,

  // CPU clock and reset
  input                             cpu_clk,
  input                             cpu_rst,

  // Wishbone interface (istruction)
  output [31:0]                     iwbm_adr_o,
  output                            iwbm_stb_o,
  output                            iwbm_cyc_o,
  output [3:0]                      iwbm_sel_o,
  output                            iwbm_we_o,
  output [2:0]                      iwbm_cti_o,
  output [1:0]                      iwbm_bte_o,
  output [31:0]                     iwbm_dat_o,
  input                             iwbm_err_i,
  input                             iwbm_ack_i,
  input [31:0]                      iwbm_dat_i,
  input                             iwbm_rty_i,

  // Wishbone interface (data)
  output [31:0]                     dwbm_adr_o,
  output                            dwbm_stb_o,
  output                            dwbm_cyc_o,
  output [3:0]                      dwbm_sel_o,
  output                            dwbm_we_o,
  output [2:0]                      dwbm_cti_o,
  output [1:0]                      dwbm_bte_o,
  output [31:0]                     dwbm_dat_o,
  input                             dwbm_err_i,
  input                             dwbm_ack_i,
  input [31:0]                      dwbm_dat_i,
  input                             dwbm_rty_i,

  // IRQ
  input [31:0]                      irq_i,

  // Debug System accesses CPU SPRs through DU
  input [15:0]                      du_addr_i,
  input                             du_stb_i,
  input [OPTION_OPERAND_WIDTH-1:0]  du_dat_i,
  input                             du_we_i,
  output [OPTION_OPERAND_WIDTH-1:0] du_dat_o,
  output                            du_ack_o,
  // Stall control from debug interface
  input                             du_stall_i,
  output                            du_stall_o,

  // The multicore core identifier
  input [OPTION_OPERAND_WIDTH-1:0]  multicore_coreid_i,
  // The number of cores
  input [OPTION_OPERAND_WIDTH-1:0]  multicore_numcores_i,

  input [31:0]                     snoop_adr_i,
  input                            snoop_en_i
);

  // DBUS-Bridge <-> CPU data port
  wire [OPTION_OPERAND_WIDTH-1:0] cpu2dbus_adr;
  wire [3:0]                      cpu2dbus_bsel;
  wire                            cpu2dbus_burst;
  wire [OPTION_OPERAND_WIDTH-1:0] cpu2dbus_dat;
  wire                            cpu2dbus_req;
  wire                            cpu2dbus_lwa_cmd; // atomic load
  wire                            cpu2dbus_stna_cmd; // none-atomic store
  wire                            cpu2dbus_swa_cmd; // atomic store
  wire                            dbus2cpu_err;
  wire                            dbus2cpu_ack;
  wire [OPTION_OPERAND_WIDTH-1:0] dbus2cpu_dat;
  wire                            dbus2cpu_burst_last;
  // Other connections for lwa/swa support
  wire                            pipeline_flush;
  wire                            dbus2cpu_atomic_flg;
  // For DCACHE snoop-invalidate
  wire [OPTION_OPERAND_WIDTH-1:0] dbus2cpu_snoop_adr;
  wire                            dbus2cpu_snoop_en;


  // IBUS-Bridge <-> CPU instruction port
  wire [OPTION_OPERAND_WIDTH-1:0] cpu2ibus_adr;
  wire                            cpu2ibus_burst;
  wire                            cpu2ibus_req;
  wire                            ibus2cpu_err;
  wire                            ibus2cpu_ack;
  wire [OPTION_OPERAND_WIDTH-1:0] ibus2cpu_dat;
  wire                            ibus2cpu_burst_last;

  // SPR access ???
  wire [15:0]                     spr_bus_addr_o;
  wire [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o;
  wire                            spr_bus_stb_o;
  wire                            spr_bus_we_o;


  // BUS-Bridge for CPU instruction port
  mor1kx_bus_if_wb32_marocchino
  #(
    .DRIVER_TYPE          ("I_CACHE"), // IBUS_BRIDGE
    .BUS_IF_TYPE          (IBUS_WB_TYPE), // IBUS_BRIDGE
    .BURST_LENGTH         ((OPTION_ICACHE_BLOCK_WIDTH == 4) ? 4 : // IBUS_BRIDGE
                           (OPTION_ICACHE_BLOCK_WIDTH == 5) ? 8 : 1), // IBUS_BRIDGE
    .OPTION_DCACHE_SNOOP  ("NONE") // IBUS_BRIDGE
  )
  ibus_bridge
  (
    // WishBone-domain: clock and reset
    .wb_clk           (wb_clk), // IBUS_BRIDGE
    .wb_rst           (wb_rst), // IBUS_BRIDGE
    // CPU-domain: clock and reset
    .cpu_clk          (cpu_clk), // IBUS_BRIDGE
    .cpu_rst          (cpu_rst), // IBUS_BRIDGE
    // For lwa/swa
    .pipeline_flush_i (1'b0), // IBUS_BRIDGE
    // CPU side
    .cpu_err_o        (ibus2cpu_err), // IBUS_BRIDGE
    .cpu_ack_o        (ibus2cpu_ack), // IBUS_BRIDGE
    .cpu_dat_o        (ibus2cpu_dat[`OR1K_INSN_WIDTH-1:0]), // IBUS_BRIDGE
    .cpu_burst_last_o (ibus2cpu_burst_last), // IBUS_BRIDGE
    .cpu_adr_i        (cpu2ibus_adr), // IBUS_BRIDGE
    .cpu_dat_i        ({OPTION_OPERAND_WIDTH{1'b0}}), // IBUS_BRIDGE
    .cpu_req_i        (cpu2ibus_req), // IBUS_BRIDGE
    .cpu_bsel_i       (4'b1111), // IBUS_BRIDGE
    .cpu_lwa_cmd_i    (1'b0), // IBUS_BRIDGE
    .cpu_stna_cmd_i   (1'b0), // IBUS_BRIDGE
    .cpu_swa_cmd_i    (1'b0), // IBUS_BRIDGE
    .cpu_burst_i      (cpu2ibus_burst), // IBUS_BRIDGE
    // Other connections for lwa/swa support
    .cpu_atomic_flg_o (), // IBUS_BRIDGE
    // For DCACHE snoop-invalidate
    .cpu_snoop_adr_o  (), // IBUS_BRIDGE
    .cpu_snoop_en_o   (), // IBUS_BRIDGE
    // Wishbone side
    .wbm_adr_o        (iwbm_adr_o), // IBUS_BRIDGE
    .wbm_stb_o        (iwbm_stb_o), // IBUS_BRIDGE
    .wbm_cyc_o        (iwbm_cyc_o), // IBUS_BRIDGE
    .wbm_sel_o        (iwbm_sel_o), // IBUS_BRIDGE
    .wbm_we_o         (iwbm_we_o), // IBUS_BRIDGE
    .wbm_cti_o        (iwbm_cti_o), // IBUS_BRIDGE
    .wbm_bte_o        (iwbm_bte_o), // IBUS_BRIDGE
    .wbm_dat_o        (iwbm_dat_o), // IBUS_BRIDGE
    .wbm_err_i        (iwbm_err_i), // IBUS_BRIDGE
    .wbm_ack_i        (iwbm_ack_i), // IBUS_BRIDGE
    .wbm_dat_i        (iwbm_dat_i), // IBUS_BRIDGE
    .wbm_rty_i        (iwbm_rty_i), // IBUS_BRIDGE
    // For lwa/swa
    .snoop_adr_i      (32'd0), // IBUS_BRIDGE
    .snoop_en_i       (1'b0) // IBUS_BRIDGE
  );

  // BUS-Bridge for CPU data port
  mor1kx_bus_if_wb32_marocchino
  #(
    .DRIVER_TYPE          ("D_CACHE"), // DBUS_BRIDGE
    .BUS_IF_TYPE          (DBUS_WB_TYPE), // DBUS_BRIDGE
    .BURST_LENGTH         ((OPTION_DCACHE_BLOCK_WIDTH == 4) ? 4 : // DBUS_BRIDGE
                           (OPTION_DCACHE_BLOCK_WIDTH == 5) ? 8 : 1), // DBUS_BRIDGE
    .OPTION_DCACHE_SNOOP  (OPTION_DCACHE_SNOOP) // DBUS_BRIDGE
  )
  dbus_bridge
  (
    // WishBone-domain: clock and reset
    .wb_clk           (wb_clk), // DBUS_BRIDGE
    .wb_rst           (wb_rst), // DBUS_BRIDGE
    // CPU-domain: clock and reset
    .cpu_clk          (cpu_clk), // DBUS_BRIDGE
    .cpu_rst          (cpu_rst), // DBUS_BRIDGE
    // For lwa/swa
    .pipeline_flush_i (pipeline_flush), // DBUS_BRIDGE
    // CPU side
    .cpu_err_o        (dbus2cpu_err), // DBUS_BRIDGE
    .cpu_ack_o        (dbus2cpu_ack), // DBUS_BRIDGE
    .cpu_dat_o        (dbus2cpu_dat), // DBUS_BRIDGE
    .cpu_burst_last_o (dbus2cpu_burst_last), // DBUS_BRIDGE
    .cpu_adr_i        (cpu2dbus_adr), // DBUS_BRIDGE
    .cpu_dat_i        (cpu2dbus_dat), // DBUS_BRIDGE
    .cpu_req_i        (cpu2dbus_req), // DBUS_BRIDGE
    .cpu_bsel_i       (cpu2dbus_bsel), // DBUS_BRIDGE
    .cpu_lwa_cmd_i    (cpu2dbus_lwa_cmd), // DBUS_BRIDGE
    .cpu_stna_cmd_i   (cpu2dbus_stna_cmd), // DBUS_BRIDGE
    .cpu_swa_cmd_i    (cpu2dbus_swa_cmd), // DBUS_BRIDGE
    .cpu_burst_i      (cpu2dbus_burst), // DBUS_BRIDGE
    // Other connections for lwa/swa support
    .cpu_atomic_flg_o (dbus2cpu_atomic_flg), // DBUS_BRIDGE
    // For DCACHE snoop-invalidate
    .cpu_snoop_adr_o  (dbus2cpu_snoop_adr), // DBUS_BRIDGE
    .cpu_snoop_en_o   (dbus2cpu_snoop_en), // DBUS_BRIDGE
    // Wishbone side
    .wbm_adr_o        (dwbm_adr_o), // DBUS_BRIDGE
    .wbm_stb_o        (dwbm_stb_o), // DBUS_BRIDGE
    .wbm_cyc_o        (dwbm_cyc_o), // DBUS_BRIDGE
    .wbm_sel_o        (dwbm_sel_o), // DBUS_BRIDGE
    .wbm_we_o         (dwbm_we_o), // DBUS_BRIDGE
    .wbm_cti_o        (dwbm_cti_o), // DBUS_BRIDGE
    .wbm_bte_o        (dwbm_bte_o), // DBUS_BRIDGE
    .wbm_dat_o        (dwbm_dat_o), // DBUS_BRIDGE
    .wbm_err_i        (dwbm_err_i), // DBUS_BRIDGE
    .wbm_ack_i        (dwbm_ack_i), // DBUS_BRIDGE
    .wbm_dat_i        (dwbm_dat_i), // DBUS_BRIDGE
    .wbm_rty_i        (dwbm_rty_i), // DBUS_BRIDGE
    // For lwa/swa
    .snoop_adr_i      (snoop_adr_i), // DBUS_BRIDGE
    .snoop_en_i       (snoop_en_i) // DBUS_BRIDGE
  );

  // instance of MAROCCHINO pipeline
  mor1kx_cpu_marocchino
  #(
    .OPTION_OPERAND_WIDTH             (OPTION_OPERAND_WIDTH), // CPU
    // temporary:
    .OPTION_ORFPX64A32_ABI            (OPTION_ORFPX64A32_ABI), // CPU
    // data cache
    .OPTION_DCACHE_BLOCK_WIDTH        (OPTION_DCACHE_BLOCK_WIDTH), // CPU
    .OPTION_DCACHE_SET_WIDTH          (OPTION_DCACHE_SET_WIDTH), // CPU
    .OPTION_DCACHE_WAYS               (OPTION_DCACHE_WAYS), // CPU
    .OPTION_DCACHE_LIMIT_WIDTH        (OPTION_DCACHE_LIMIT_WIDTH), // CPU
    .OPTION_DCACHE_SNOOP              (OPTION_DCACHE_SNOOP), // CPU
    .OPTION_DCACHE_CLEAR_ON_INIT      (OPTION_DCACHE_CLEAR_ON_INIT), // CPU
    // data mmu
    .FEATURE_DMMU_HW_TLB_RELOAD       (FEATURE_DMMU_HW_TLB_RELOAD), // CPU
    .OPTION_DMMU_SET_WIDTH            (OPTION_DMMU_SET_WIDTH), // CPU
    .OPTION_DMMU_WAYS                 (OPTION_DMMU_WAYS), // CPU
    .OPTION_DMMU_CLEAR_ON_INIT        (OPTION_DMMU_CLEAR_ON_INIT), // CPU
    // write buffer
    .OPTION_STORE_BUFFER_DEPTH_WIDTH    (OPTION_STORE_BUFFER_DEPTH_WIDTH), // CPU
    .OPTION_STORE_BUFFER_CLEAR_ON_INIT  (OPTION_STORE_BUFFER_CLEAR_ON_INIT), // CPU
    // instruction cache
    .OPTION_ICACHE_BLOCK_WIDTH        (OPTION_ICACHE_BLOCK_WIDTH), // CPU
    .OPTION_ICACHE_SET_WIDTH          (OPTION_ICACHE_SET_WIDTH), // CPU
    .OPTION_ICACHE_WAYS               (OPTION_ICACHE_WAYS),
    .OPTION_ICACHE_LIMIT_WIDTH        (OPTION_ICACHE_LIMIT_WIDTH), // CPU
    .OPTION_ICACHE_CLEAR_ON_INIT      (OPTION_ICACHE_CLEAR_ON_INIT), // CPU
    // instruction mmu
    .FEATURE_IMMU_HW_TLB_RELOAD       (FEATURE_IMMU_HW_TLB_RELOAD), // CPU
    .OPTION_IMMU_SET_WIDTH            (OPTION_IMMU_SET_WIDTH), // CPU
    .OPTION_IMMU_WAYS                 (OPTION_IMMU_WAYS), // CPU
    .OPTION_IMMU_CLEAR_ON_INIT        (OPTION_IMMU_CLEAR_ON_INIT), // CPU
    // interrupt controller
    .OPTION_PIC_TRIGGER               (OPTION_PIC_TRIGGER), // CPU
    .OPTION_PIC_NMI_WIDTH             (OPTION_PIC_NMI_WIDTH), // CPU
    // timer, debug unit, performance counters, trace
    .FEATURE_DEBUGUNIT                (FEATURE_DEBUGUNIT), // CPU
    .FEATURE_PERFCOUNTERS             (FEATURE_PERFCOUNTERS), // CPU
    // m-core
    .FEATURE_MULTICORE                (FEATURE_MULTICORE), // CPU
    .OPTION_RF_NUM_SHADOW_GPR         (OPTION_RF_NUM_SHADOW_GPR), // CPU
    // Redister File
    .OPTION_RF_CLEAR_ON_INIT          (OPTION_RF_CLEAR_ON_INIT), // CPU
    .OPTION_RF_ADDR_WIDTH             (OPTION_RF_ADDR_WIDTH), // CPU
    //.OPTION_RF_WORDS(OPTION_RF_WORDS), // MAROCCHINO_TODO
    // starting PC
    .OPTION_RESET_PC                  (OPTION_RESET_PC), // CPU
     // special instructions
    .FEATURE_PSYNC                    (FEATURE_PSYNC), // CPU
    .FEATURE_CSYNC                    (FEATURE_CSYNC) // CPU
  )
  u_cpu_marocchino
  (
    // Wishbone clock and reset
    .wb_clk                   (wb_clk), // CPU
    .wb_rst                   (wb_rst), // CPU
    // CPU clock and reset
    .cpu_clk                  (cpu_clk), // CPU
    .cpu_rst                  (cpu_rst), // CPU
    // For lwa/swa
    .pipeline_flush_o         (pipeline_flush), // CPU
    // Instruction bus
    .ibus_adr_o               (cpu2ibus_adr), // CPU
    .ibus_req_o               (cpu2ibus_req), // CPU
    .ibus_burst_o             (cpu2ibus_burst), // CPU
    .ibus_err_i               (ibus2cpu_err), // CPU
    .ibus_ack_i               (ibus2cpu_ack), // CPU
    .ibus_dat_i               (ibus2cpu_dat[`OR1K_INSN_WIDTH-1:0]), // CPU
    .ibus_burst_last_i        (ibus2cpu_burst_last), // CPU
    // Data bus
    .dbus_adr_o               (cpu2dbus_adr), // CPU
    .dbus_dat_o               (cpu2dbus_dat), // CPU
    .dbus_req_o               (cpu2dbus_req), // CPU
    .dbus_bsel_o              (cpu2dbus_bsel), // CPU
    .dbus_lwa_cmd_o           (cpu2dbus_lwa_cmd), // CPU
    .dbus_stna_cmd_o          (cpu2dbus_stna_cmd), // CPU
    .dbus_swa_cmd_o           (cpu2dbus_swa_cmd), // CPU
    .dbus_burst_o             (cpu2dbus_burst), // CPU
    .dbus_err_i               (dbus2cpu_err), // CPU
    .dbus_ack_i               (dbus2cpu_ack), // CPU
    .dbus_dat_i               (dbus2cpu_dat), // CPU
    .dbus_burst_last_i        (dbus2cpu_burst_last), // CPU
    // Other connections for lwa/swa support
    .dbus_atomic_flg_i        (dbus2cpu_atomic_flg), // CPU
    // Interrupts
    .irq_i                    (irq_i[31:0]), // CPU
    // Debug interface
    .du_dat_o                 (du_dat_o), // CPU
    .du_ack_o                 (du_ack_o), // CPU
    .du_addr_i                (du_addr_i), // CPU
    .du_stb_i                 (du_stb_i), // CPU
    .du_dat_i                 (du_dat_i), // CPU
    .du_we_i                  (du_we_i), // CPU
    // Stall control from debug interface
    .du_stall_i               (du_stall_i), // CPU
    .du_stall_o               (du_stall_o), // CPU
    // SPR accesses to external units (cache, mmu, etc.)
    .spr_bus_addr_o           (spr_bus_addr_o[15:0]), // CPU
    .spr_bus_we_o             (spr_bus_we_o), // CPU
    .spr_bus_stb_o            (spr_bus_stb_o), // CPU
    .spr_bus_dat_o            (spr_bus_dat_o), // CPU
    // multi-core
    .multicore_coreid_i       (multicore_coreid_i), // CPU
    .multicore_numcores_i     (multicore_numcores_i), // CPU
    .snoop_adr_i              (dbus2cpu_snoop_adr), // CPU
    .snoop_en_i               (dbus2cpu_snoop_en) // CPU
  ); // pipe instance

endmodule // mor1kx_top_marocchino
