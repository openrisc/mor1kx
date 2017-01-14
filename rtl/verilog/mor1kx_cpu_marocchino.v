////////////////////////////////////////////////////////////////////////
//                                                                    //
//  mor1kx_cpu_marocchino                                             //
//                                                                    //
//  Description: MAROCCHINO pipeline CPU module                       //
//               Derived from mor1kx_cpu_cappuccino                   //
//                                                                    //
////////////////////////////////////////////////////////////////////////
//                                                                    //
//   Copyright (C) 2012 Julius Baxter                                 //
//                      juliusbaxter@gmail.com                        //
//                                                                    //
//   Copyright (C) 2015 - 2016 Andrey Bacherov                        //
//                             avbacherov@opencores.org               //
//                                                                    //
//      This Source Code Form is subject to the terms of the          //
//      Open Hardware Description License, v. 1.0. If a copy          //
//      of the OHDL was not distributed with this file, You           //
//      can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt       //
//                                                                    //
////////////////////////////////////////////////////////////////////////

`include "mor1kx-defines.v"

module mor1kx_cpu_marocchino
#(
  parameter OPTION_OPERAND_WIDTH = 32,
  // data cache
  parameter OPTION_DCACHE_BLOCK_WIDTH   = 5,
  parameter OPTION_DCACHE_SET_WIDTH     = 9,
  parameter OPTION_DCACHE_WAYS          = 2,
  parameter OPTION_DCACHE_LIMIT_WIDTH   = 32,
  parameter OPTION_DCACHE_SNOOP         = "NONE",
  parameter OPTION_DCACHE_CLEAR_ON_INIT = 0,
  // data mmu
  parameter FEATURE_DMMU_HW_TLB_RELOAD  = "NONE",
  parameter OPTION_DMMU_SET_WIDTH       = 6,
  parameter OPTION_DMMU_WAYS            = 1,
  parameter OPTION_DMMU_CLEAR_ON_INIT   = 0,
  // instruction cache
  parameter OPTION_ICACHE_BLOCK_WIDTH   = 5,
  parameter OPTION_ICACHE_SET_WIDTH     = 9,
  parameter OPTION_ICACHE_WAYS          = 2,
  parameter OPTION_ICACHE_LIMIT_WIDTH   = 32,
  parameter OPTION_ICACHE_CLEAR_ON_INIT = 0,
  // instruction mmu
  parameter FEATURE_IMMU_HW_TLB_RELOAD  = "NONE",
  parameter OPTION_IMMU_SET_WIDTH       = 6,
  parameter OPTION_IMMU_WAYS            = 1,
  parameter OPTION_IMMU_CLEAR_ON_INIT   = 0,

  parameter FEATURE_DEBUGUNIT    = "NONE",
  parameter FEATURE_PERFCOUNTERS = "NONE",

  parameter OPTION_PIC_TRIGGER   = "LEVEL",
  parameter OPTION_PIC_NMI_WIDTH = 0,

  parameter OPTION_RF_CLEAR_ON_INIT  = 0,
  parameter OPTION_RF_ADDR_WIDTH     = 5,

  parameter OPTION_RESET_PC = {{(OPTION_OPERAND_WIDTH-13){1'b0}},
                              `OR1K_RESET_VECTOR,8'd0},

  parameter FEATURE_PSYNC = "NONE",
  parameter FEATURE_CSYNC = "NONE",

  parameter OPTION_STORE_BUFFER_DEPTH_WIDTH   = 4, // 16 taps
  parameter OPTION_STORE_BUFFER_CLEAR_ON_INIT = 0,

  parameter FEATURE_MULTICORE      = "NONE",

  parameter FEATURE_TRACEPORT_EXEC = "NONE"
)
(
  input                             clk,
  input                             rst,

  // Instruction bus
  input                             ibus_err_i,
  input                             ibus_ack_i,
  input      [`OR1K_INSN_WIDTH-1:0] ibus_dat_i,
  output [OPTION_OPERAND_WIDTH-1:0] ibus_adr_o,
  output                            ibus_req_o,
  output                            ibus_burst_o,

  // Data bus
  input                             dbus_err_i,
  input                             dbus_ack_i,
  input  [OPTION_OPERAND_WIDTH-1:0] dbus_dat_i,
  output [OPTION_OPERAND_WIDTH-1:0] dbus_adr_o,
  output [OPTION_OPERAND_WIDTH-1:0] dbus_dat_o,
  output                            dbus_req_o,
  output                      [3:0] dbus_bsel_o,
  output                            dbus_we_o,
  output                            dbus_burst_o,

  // Interrupts
  input                      [31:0] irq_i,

  // Debug interface
  input                      [15:0] du_addr_i,
  input                             du_stb_i,
  input  [OPTION_OPERAND_WIDTH-1:0] du_dat_i,
  input                             du_we_i,
  output [OPTION_OPERAND_WIDTH-1:0] du_dat_o,
  output                            du_ack_o,
  // Stall control from debug interface
  input                             du_stall_i,
  output                            du_stall_o,

  output reg                        traceport_exec_valid_o,
  output reg                 [31:0] traceport_exec_pc_o,
  output reg [`OR1K_INSN_WIDTH-1:0] traceport_exec_insn_o,
  output [OPTION_OPERAND_WIDTH-1:0] traceport_exec_wbdata_o,
  output [OPTION_RF_ADDR_WIDTH-1:0] traceport_exec_wbreg_o,
  output                            traceport_exec_wben_o,

  // SPR accesses to external units (cache, mmu, etc.)
  output [15:0]                     spr_bus_addr_o,
  output                            spr_bus_we_o,
  output                            spr_bus_stb_o,
  output [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o,

  input  [OPTION_OPERAND_WIDTH-1:0] multicore_coreid_i,
  input  [OPTION_OPERAND_WIDTH-1:0] multicore_numcores_i,

  input                      [31:0] snoop_adr_i,
  input                             snoop_en_i
);

  localparam DEST_EXT_ADDR_WIDTH  = 3; // log2(Re-Ordering buffer width)
  localparam DEST_REG_ADDR_WIDTH  = OPTION_RF_ADDR_WIDTH + DEST_EXT_ADDR_WIDTH;


  wire     [`OR1K_INSN_WIDTH-1:0] dcod_insn;
  wire                            dcod_insn_valid;

  wire [OPTION_OPERAND_WIDTH-1:0] pc_decode;
  wire [OPTION_OPERAND_WIDTH-1:0] pc_exec;
  wire [OPTION_OPERAND_WIDTH-1:0] pc_wb;

  wire                            wb_atomic_flag_set;
  wire                            wb_atomic_flag_clear;

  wire                            wb_int_flag_set;
  wire                            wb_int_flag_clear;

  wire                            ctrl_flag;
  wire                            ctrl_carry;

  wire                            dcod_flag_wb; // instruction writes comparison flag
  wire                            dcod_carry_wb; // instruction writes carry flag

  wire                            dcod_flag_req;  // instructions require comparison flag
  wire                            dcod_carry_req; // instructions require carry flag

  wire                            dcod_op_mfspr; // to OMAN & CTRL (not latched)
  wire                            dcod_op_mtspr; // to OMAN & CTRL (not latched)


  wire [OPTION_OPERAND_WIDTH-1:0] wb_alu_1clk_result;
  wire [OPTION_OPERAND_WIDTH-1:0] wb_div_result;
  wire [OPTION_OPERAND_WIDTH-1:0] wb_mul_result;
  wire [OPTION_OPERAND_WIDTH-1:0] wb_fpxx_arith_res_hi;
  wire [OPTION_OPERAND_WIDTH-1:0] wb_fpxx_arith_res_lo;
  wire [OPTION_OPERAND_WIDTH-1:0] wb_lsu_result;
  wire [OPTION_OPERAND_WIDTH-1:0] wb_mfspr_dat;
  wire [OPTION_OPERAND_WIDTH-1:0] wb_result1; // WB result combiner
  wire [OPTION_OPERAND_WIDTH-1:0] wb_result2; // WB result combiner for FPU64


  wire                            dcod_valid;
  wire                            exec_valid;
  wire                            lsu_valid;   // result ready or exceptions
  wire                            wb_lsu_valid_miss; // speculative WB for LSU


  // D1 related WB-to-DECODE hazards for LSU WB miss processing
  wire                            dcod_wb2dec_eq_adr_d1a1;
  wire                            dcod_wb2dec_eq_adr_d1b1;
  wire                            dcod_wb2dec_eq_adr_d1a2;
  wire                            dcod_wb2dec_eq_adr_d1b2;
  // D1 related EXECUTE-to-DECODE hazards for LSU WB miss processing
  wire                            exec_wb2exe_hazard_d1xx_1clk; // specially for l.bf/l.bnf


  wire [OPTION_OPERAND_WIDTH-1:0] dcod_rfa1;
  wire [OPTION_OPERAND_WIDTH-1:0] dcod_rfb1;
  wire [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa1_adr;
  wire [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb1_adr;
  wire                            dcod_rfa1_req;
  wire                            dcod_rfb1_req;
  wire [OPTION_OPERAND_WIDTH-1:0] dcod_immediate;
  wire                            dcod_immediate_sel;
  // Special case for l.jr/l.jalr
  wire [OPTION_OPERAND_WIDTH-1:0] dcod_rfb1_jr;
  // for FPU64:
  wire [OPTION_OPERAND_WIDTH-1:0] dcod_rfa2;
  wire [OPTION_OPERAND_WIDTH-1:0] dcod_rfb2;
  wire [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa2_adr;
  wire [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb2_adr;
  wire                            dcod_rfa2_req;
  wire                            dcod_rfb2_req;


  wire [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfd1_adr;
  wire                            dcod_rfd1_wb;
  // for FPU64:
  wire [OPTION_RF_ADDR_WIDTH-1:0] insn_rfd2_adr;
  wire [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfd2_adr;


  // OMAN-to-DECODE hazards
  //  combined flag
  wire                            omn2dec_a_hazard_lsu;
  wire                            omn2dec_a_hazard_1clk;
  wire                            omn2dec_a_hazard_mclk;
  //  by FLAG and CARRY
  wire                            busy_hazard_f;
  wire  [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_f_adr;
  wire                            busy_hazard_c;
  wire  [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_c_adr;
  //  by operands
  wire                            busy_hazard_d1a1;
  wire  [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d1a1_adr;
  wire                            busy_hazard_d1b1;
  wire  [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d1b1_adr;
  wire                            busy_hazard_d2a1;
  wire  [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d2a1_adr;
  wire                            busy_hazard_d2b1;
  wire  [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d2b1_adr;
  wire                            busy_hazard_d1a2;
  wire  [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d1a2_adr;
  wire                            busy_hazard_d1b2;
  wire  [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d1b2_adr;
  wire                            busy_hazard_d2a2;
  wire  [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d2a2_adr;
  wire                            busy_hazard_d2b2;
  wire  [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d2b2_adr;
  // EXEC-to-DECODE hazards
  //  combined flag
  wire                            exe2dec_a_hazard_lsu;
  wire                            exe2dec_a_hazard_1clk;
  wire                            exe2dec_a_hazard_mclk;
  //  by operands
  wire                            exe2dec_hazard_d1a1;
  wire                            exe2dec_hazard_d1b1;
  wire                            exe2dec_hazard_d2a1;
  wire                            exe2dec_hazard_d2b1;
  wire                            exe2dec_hazard_d1a2;
  wire                            exe2dec_hazard_d1b2;
  wire                            exe2dec_hazard_d2a2;
  wire                            exe2dec_hazard_d2b2;
  // Hazard could be passed from DECODE to EXECUTE
  wire                            exec_flag_wb;
  wire                            exec_carry_wb;
  wire                            exec_rfd1_wb;
  wire                            exec_rfd2_wb;
  wire  [DEST_EXT_ADDR_WIDTH-1:0] exec_ext_adr;
  // Hazard could be resolving
  //  ## FLAG or CARRY
  wire                            wb_flag_wb;
  wire                            wb_flag_wb_lsu_miss; // speculative WB for l.swa miss
  wire                            wb_carry_wb;
  //  ## A or B operand
  wire                            wb_rfd1_wb_lsu_miss; // speculative WB for LSU miss
  wire                            wb_rfd1_wb;
  wire  [DEST_REG_ADDR_WIDTH-1:0] wb_rfd1_adr;
  //  ## for FPU64
  wire                            wb_rfd2_wb;  // WB instruction is writting RF
  wire [OPTION_RF_ADDR_WIDTH-1:0] wb_rfd2_adr; // low part of A or B operand

  wire                            dcod_op_jr;
  wire                            fetch_waiting_target;

  wire                            dcod_delay_slot;
  wire                            wb_delay_slot;


  // branching
  //  ## detect jump/branch to indicate "delay slot" for next fetched instruction
  wire                            dcod_jump_or_branch;
  //  ## support IBUS error handling in CTRL
  wire                            exec_jump_or_branch;
  //  ## do branch (pedicted or unconditional)
  wire                            dcod_do_branch;
  wire [OPTION_OPERAND_WIDTH-1:0] dcod_do_branch_target;

  // Signals to stall FETCH if we are waiting flag
  //  # flag is going to be written by multi-cycle instruction
  //  # like 64-bit FPU comparison or l.swa
  wire                            dcod_flag_wb_mcycle;
  //  # conditional branch: l.bf or l.bnf
  wire                            dcod_op_brcond;



  wire      [`OR1K_IMM_WIDTH-1:0] dcod_imm16;
  wire                            dcod_op_lsu_load;
  wire                            dcod_op_lsu_store;
  wire                            dcod_op_lsu_atomic;
  wire                      [1:0] dcod_lsu_length;
  wire                            dcod_lsu_zext;
  wire                            dcod_op_msync;
  wire                            lsu_busy;
  wire                            grant_wb_to_lsu;


  // Instruction which passes EXECUTION through
  wire                            dcod_op_pass_exec;


  // Reservation station for 1-clock execution units
  wire                            dcod_op_1clk;
  wire                            op_1clk_busy;
  wire  [`OR1K_ALU_OPC_WIDTH-1:0] dcod_opc_alu_secondary;

  wire                            dcod_op_add;
  wire                            dcod_adder_do_sub;
  wire                            dcod_adder_do_carry;

  wire                            dcod_op_jal;
  wire [OPTION_OPERAND_WIDTH-1:0] dcod_jal_result;

  wire                            dcod_op_shift;
  wire                            dcod_op_ffl1;
  wire                            dcod_op_movhi;
  wire                            dcod_op_cmov;

  wire  [`OR1K_ALU_OPC_WIDTH-1:0] dcod_opc_logic;

  wire                            dcod_op_setflag;

  wire                            exec_op_1clk;
  wire                            grant_wb_to_1clk;


  // Reservation station for multi-clocks execution units
  wire                            mclk_busy;

  // Divider
  wire                            dcod_op_div;
  wire                            dcod_op_div_signed;
  wire                            dcod_op_div_unsigned;
  wire                            div_valid;
  wire                            grant_wb_to_div;


  // Pipelined multiplier
  wire                            dcod_op_mul;
  wire                            mul_valid;
  wire                            grant_wb_to_mul;

  // FPU-32 comparison part
  wire                            dcod_op_fp32_cmp;
  wire                      [2:0] dcod_opc_fp32_cmp;
  wire                            wb_fp32_flag_set;
  wire                            wb_fp32_flag_clear;
  wire                            wb_fp32_cmp_inv;
  wire                            wb_fp32_cmp_inf;
  wire                            wb_fp32_cmp_wb_fpcsr;
  wire                            wb_except_fp32_cmp;

  // FPU3264 arithmetic part
  wire                              dcod_op_fpxx_arith; // to OMAN and FPU3264_ARITH
  wire                              dcod_op_fp64_arith; // to OMAN and FPU3264_ARITH
  wire                              dcod_op_fpxx_add; // to FPU3264_ARITH
  wire                              dcod_op_fpxx_sub; // to FPU3264_ARITH
  wire                              dcod_op_fpxx_mul; // to FPU3264_ARITH
  wire                              dcod_op_fpxx_div; // to FPU3264_ARITH
  wire                              dcod_op_fpxx_i2f; // to FPU3264_ARITH
  wire                              dcod_op_fpxx_f2i; // to FPU3264_ARITH
  wire                              fpxx_arith_valid;
  wire                              grant_wb_to_fpxx_arith;
  wire  [`OR1K_FPCSR_ALLF_SIZE-1:0] wb_fpxx_arith_fpcsr;    // only flags
  wire                              wb_fpxx_arith_wb_fpcsr; // update FPCSR
  wire                              wb_except_fpxx_arith;   // generate FPx exception by FPx flags

  // FPU-64 comparison part
  wire                            dcod_op_fp64_cmp;
  wire                      [2:0] dcod_opc_fp64_cmp;
  wire                            exec_op_fp64_cmp;
  wire                      [2:0] exec_opc_fp64_cmp;
  wire                            grant_wb_to_fp64_cmp;
  wire                            wb_fp64_flag_set;
  wire                            wb_fp64_flag_clear;
  wire                            wb_fp64_cmp_inv;
  wire                            wb_fp64_cmp_inf;
  wire                            wb_fp64_cmp_wb_fpcsr;
  wire                            wb_except_fp64_cmp;

  // Forwarding comparision flag
  wire                            busy_op_1clk_cmp; // integer or fp32
  // # either l.sf* or lf.sf*
  //   !!! MUST BE in [0] of OPC-word of reservation station
  wire                            exec_op_1clk_cmp;
  // integer or fp32 comparison result
  wire                            exec_flag_set;


  wire [OPTION_OPERAND_WIDTH-1:0] sbuf_eear;
  wire [OPTION_OPERAND_WIDTH-1:0] sbuf_epcr;
  wire                            sbuf_err;


  // SPR access buses (Unit -> CTRL part)
  //   GPR
  wire                            spr_bus_ack_gpr;
  wire [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_gpr;
  //   Data MMU
  wire [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_dmmu;
  wire                            spr_bus_ack_dmmu;
  //   Data Cache
  wire [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_dc;
  wire                            spr_bus_ack_dc;
  //   Insn MMU
  wire [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_immu;
  wire                            spr_bus_ack_immu;
  //   Insn Cache
  wire [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_ic;
  wire                            spr_bus_ack_ic;


  // pipeline controls from CTRL to units
  wire padv_fetch;
  wire padv_decode;
  wire padv_wb;
  wire pipeline_flush;

  // enable modules and other control signals from CTRL
  wire                            ic_enable;
  wire                            immu_enable;
  wire                            dc_enable;
  wire                            dmmu_enable;
  wire                            supervisor_mode;

  // FPU related controls
  wire                             except_fpu_enable;
  wire [`OR1K_FPCSR_ALLF_SIZE-1:0] ctrl_fpu_mask_flags;
  wire   [`OR1K_FPCSR_RM_SIZE-1:0] ctrl_fpu_round_mode;


  // Exceptions: reported by IFETCH
  //  # connections IFETCH->OMAN
  wire fetch_except_ibus_err;
  wire fetch_except_ipagefault;
  wire fetch_except_itlb_miss;
  wire fetch_except_ibus_align;
  //  # connections OMAN(WB-latches)->CTRL
  wire wb_except_ibus_err;
  wire wb_except_ipagefault;
  wire wb_except_itlb_miss;
  wire wb_except_ibus_align;

  // Exceptions: reported from DECODE to OMAN
  wire dcod_except_illegal;
  wire dcod_except_syscall;
  wire dcod_except_trap;
  // Enable l.trap exception
  wire du_trap_enable;
  // Exceptions: latched by WB latches for processing in CONTROL-unit
  wire wb_except_illegal;
  wire wb_except_syscall;
  wire wb_except_trap;

  // IFETCH/EXECETE exceptions flags are used to slall fetching and
  // decoding new insructions till l.rfe / exception reach WRITE-BACK
  wire fetch_an_except; // latched IFETCH exceptions visible in DECODE stage
  wire exec_an_except;  // latched l.rfe + IFETCH/DECODE exceptions visible in EXECUTE stage
  wire wb_fd_an_except; // latched l.rfe + IFETCH/DECODE exceptions visible in WRITE-BACK stage

  //  # overflow exception
  wire except_overflow_enable;
  wire wb_except_overflow_div;
  wire wb_except_overflow_1clk;

  // Exceptions: reported by LSU
  //  # particular LSU exception flags
  wire                            wb_except_dbus_err;
  wire                            wb_except_dpagefault;
  wire                            wb_except_dtlb_miss;
  wire                            wb_except_dbus_align;
  wire [OPTION_OPERAND_WIDTH-1:0] wb_lsu_except_addr;
  //  # combined LSU exceptions flag
  wire                            wb_an_except_lsu;


  // External Interrupts Collection
  //  # from "Tick Timer"
  wire        tt_rdy;
  wire        tt_interrupt_enable;
  //  # from "Programmble Interrupt Controller"
  wire [31:0] spr_picsr;
  wire        pic_interrupt_enable;
  //  # flag to enabel/disable exterlal interrupts processing
  //    depending on the fact is instructions restartable or not
  wire        exec_interrupts_en;
  //  # WB latches
  reg         wb_tt_interrupt_r;
  reg         wb_pic_interrupt_r;
  reg         wb_an_interrupt_r; // from PIC or TT


  // Exeptions process:
  wire dcod_op_rfe;
  wire wb_op_rfe;
  wire ctrl_branch_exception;
  wire [OPTION_OPERAND_WIDTH-1:0] ctrl_branch_except_pc;
  //   exeptions process: fetch->ctrl
  wire fetch_ecxeption_taken;


  // FETCH none latched outputs
  wire                            fetch_rf_adr_valid; // fetch->rf
  wire [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfa1_adr;     // fetch->rf
  wire [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfb1_adr;     // fetch->rf
  // for FPU64
  wire [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfa2_adr;     // fetch->rf
  wire [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfb2_adr;     // fetch->rf


  mor1kx_fetch_marocchino
  #(
    .OPTION_OPERAND_WIDTH             (OPTION_OPERAND_WIDTH), // FETCH
    .OPTION_RESET_PC                  (OPTION_RESET_PC), // FETCH
    // ICACHE configuration
    .OPTION_ICACHE_BLOCK_WIDTH        (OPTION_ICACHE_BLOCK_WIDTH), // FETCH
    .OPTION_ICACHE_SET_WIDTH          (OPTION_ICACHE_SET_WIDTH), // FETCH
    .OPTION_ICACHE_WAYS               (OPTION_ICACHE_WAYS), // FETCH
    .OPTION_ICACHE_LIMIT_WIDTH        (OPTION_ICACHE_LIMIT_WIDTH), // FETCH
    .OPTION_ICACHE_CLEAR_ON_INIT      (OPTION_ICACHE_CLEAR_ON_INIT), // FETCH
    // IMMU configuration
    .FEATURE_IMMU_HW_TLB_RELOAD       (FEATURE_IMMU_HW_TLB_RELOAD), // FETCH
    .OPTION_IMMU_SET_WIDTH            (OPTION_IMMU_SET_WIDTH), // FETCH
    .OPTION_IMMU_WAYS                 (OPTION_IMMU_WAYS), // FETCH
    .OPTION_IMMU_CLEAR_ON_INIT        (OPTION_IMMU_CLEAR_ON_INIT) // FETCH
  )
  u_fetch
  (
    // clocks & resets
    .clk                              (clk), // FETCH
    .rst                              (rst), // FETCH

    // pipeline control
    .padv_fetch_i                     (padv_fetch), // FETCH
    .fetch_waiting_target_i           (fetch_waiting_target), // FETCH
    .pipeline_flush_i                 (pipeline_flush), // FETCH

    // configuration
    .ic_enable_i                      (ic_enable), // FETCH
    .immu_enable_i                    (immu_enable), // FETCH
    .supervisor_mode_i                (supervisor_mode), // FETCH

    // SPR interface
    //  input
    .spr_bus_addr_i                   (spr_bus_addr_o), // FETCH
    .spr_bus_we_i                     (spr_bus_we_o), // FETCH
    .spr_bus_stb_i                    (spr_bus_stb_o), // FETCH
    .spr_bus_dat_i                    (spr_bus_dat_o), // FETCH
    //  output from cache
    .spr_bus_dat_ic_o                 (spr_bus_dat_ic), // FETCH
    .spr_bus_ack_ic_o                 (spr_bus_ack_ic), // FETCH
    //  output from immu
    .spr_bus_dat_immu_o               (spr_bus_dat_immu), // FETCH
    .spr_bus_ack_immu_o               (spr_bus_ack_immu), // FETCH

    // interface to ibus
    .ibus_err_i                       (ibus_err_i), // FETCH
    .ibus_ack_i                       (ibus_ack_i), // FETCH
    .ibus_dat_i                       (ibus_dat_i[`OR1K_INSN_WIDTH-1:0]), // FETCH
    .ibus_req_o                       (ibus_req_o), // FETCH
    .ibus_adr_o                       (ibus_adr_o), // FETCH
    .ibus_burst_o                     (ibus_burst_o), // FETCH

    // branch/jump control transfer
    //  ## detect jump/branch to indicate "delay slot" for next fetched instruction
    .dcod_jump_or_branch_i            (dcod_jump_or_branch), // FETCH
    //  ## do branch (pedicted or unconditional)
    .dcod_do_branch_i                 (dcod_do_branch), // FETCH
    .dcod_do_branch_target_i          (dcod_do_branch_target), // FETCH

    // DU/exception/rfe control transfer
    .ctrl_branch_exception_i          (ctrl_branch_exception), // FETCH
    .ctrl_branch_except_pc_i          (ctrl_branch_except_pc), // FETCH

    //   To RF
    .fetch_rf_adr_valid_o             (fetch_rf_adr_valid), // FETCH (bus-access-done & padv-fetch)
    .fetch_rfa1_adr_o                 (fetch_rfa1_adr), // FETCH (not latched, to RF)
    .fetch_rfb1_adr_o                 (fetch_rfb1_adr), // FETCH (not latched, to RF)
    // for FPU64
    .fetch_rfa2_adr_o                 (fetch_rfa2_adr), // FETCH (not latched, to RF)
    .fetch_rfb2_adr_o                 (fetch_rfb2_adr), // FETCH (not latched, to RF)

    //   To DECODE
    .dcod_insn_valid_o                (dcod_insn_valid), // FETCH
    .pc_decode_o                      (pc_decode), // FETCH
    .dcod_insn_o                      (dcod_insn), // FETCH
    .dcod_delay_slot_o                (dcod_delay_slot), // FETCH
    .dcod_rfa1_adr_o                  (dcod_rfa1_adr), // FETCH
    .dcod_rfb1_adr_o                  (dcod_rfb1_adr), // FETCH
    // for FPU64
    .dcod_rfa2_adr_o                  (dcod_rfa2_adr), // FETCH
    .dcod_rfb2_adr_o                  (dcod_rfb2_adr), // FETCH
    .insn_rfd2_adr_o                  (insn_rfd2_adr), // FETCH

    //   Exceptions
    .fetch_except_ibus_err_o          (fetch_except_ibus_err), // FETCH
    .fetch_except_itlb_miss_o         (fetch_except_itlb_miss), // FETCH
    .fetch_except_ipagefault_o        (fetch_except_ipagefault), // FETCH
    .fetch_an_except_o                (fetch_an_except), // FETCH
    .fetch_exception_taken_o          (fetch_ecxeption_taken) // FETCH
  );


  //-------------------------------//
  // Registers File (GPR) instance //
  //-------------------------------//

  mor1kx_rf_marocchino
  #(
    .OPTION_OPERAND_WIDTH           (OPTION_OPERAND_WIDTH), // RF
    .OPTION_RF_CLEAR_ON_INIT        (OPTION_RF_CLEAR_ON_INIT), // RF
    .OPTION_RF_ADDR_WIDTH           (OPTION_RF_ADDR_WIDTH), // RF
    .FEATURE_DEBUGUNIT              (FEATURE_DEBUGUNIT) // RF
  )
  u_rf
  (
    // clocks & resets
    .clk                              (clk), // RF
    .rst                              (rst), // RF
    // pipeline control signals
    .pipeline_flush_i                 (pipeline_flush), // RF
    // SPR bus
    .spr_bus_addr_i                   (spr_bus_addr_o), // RF
    .spr_bus_stb_i                    (spr_bus_stb_o), // RF
    .spr_bus_we_i                     (spr_bus_we_o), // RF
    .spr_bus_dat_i                    (spr_bus_dat_o), // RF
    .spr_bus_ack_gpr_o                (spr_bus_ack_gpr), // RF
    .spr_bus_dat_gpr_o                (spr_bus_dat_gpr), // RF
    // from FETCH
    .fetch_rf_adr_valid_i             (fetch_rf_adr_valid), // RF
    .fetch_rfa1_adr_i                 (fetch_rfa1_adr), // RF
    .fetch_rfb1_adr_i                 (fetch_rfb1_adr), // RF
    // for FPU64
    .fetch_rfa2_adr_i                 (fetch_rfa2_adr), // RF
    .fetch_rfb2_adr_i                 (fetch_rfb2_adr), // RF
    // from DECODE
    .dcod_rfa1_req_i                  (dcod_rfa1_req), // RF
    .dcod_rfa1_adr_i                  (dcod_rfa1_adr), // RF
    .dcod_rfb1_req_i                  (dcod_rfb1_req), // RF
    .dcod_rfb1_adr_i                  (dcod_rfb1_adr), // RF
    .dcod_immediate_i                 (dcod_immediate), // RF
    .dcod_immediate_sel_i             (dcod_immediate_sel), // RF
    // for FPU64
    .dcod_rfa2_req_i                  (dcod_rfa2_req), // RF
    .dcod_rfa2_adr_i                  (dcod_rfa2_adr), // RF
    .dcod_rfb2_req_i                  (dcod_rfb2_req), // RF
    .dcod_rfb2_adr_i                  (dcod_rfb2_adr), // RF
    // from WB
    .wb_rfd1_wb_i                     (wb_rfd1_wb), // RF
    .wb_rfd1_adr_i                    (wb_rfd1_adr[(OPTION_RF_ADDR_WIDTH-1):0]), // RF
    .wb_result1_i                     (wb_result1), // RF
    // for FPU64
    .wb_rfd2_wb_i                     (wb_rfd2_wb), // RF
    .wb_rfd2_adr_i                    (wb_rfd2_adr), // RF
    .wb_result2_i                     (wb_result2), // RF
    // D1 related WB-to-DECODE hazards for LSU WB miss processing
    .dcod_wb2dec_eq_adr_d1a1_o        (dcod_wb2dec_eq_adr_d1a1), // RF
    .dcod_wb2dec_eq_adr_d1b1_o        (dcod_wb2dec_eq_adr_d1b1), // RF
    .dcod_wb2dec_eq_adr_d1a2_o        (dcod_wb2dec_eq_adr_d1a2), // RF
    .dcod_wb2dec_eq_adr_d1b2_o        (dcod_wb2dec_eq_adr_d1b2), // RF
    // Operands
    .dcod_rfa1_o                      (dcod_rfa1), // RF
    .dcod_rfb1_o                      (dcod_rfb1), // RF
    .dcod_rfa2_o                      (dcod_rfa2), // RF
    .dcod_rfb2_o                      (dcod_rfb2), // RF
    // Special case for l.jr/l.jalr
    .dcod_rfb1_jr_o                   (dcod_rfb1_jr) // RF
  );


  //--------//
  // DECODE //
  //--------//

  mor1kx_decode_marocchino
  #(
    .OPTION_OPERAND_WIDTH             (OPTION_OPERAND_WIDTH), // DECODE & DECODE->EXE
    .OPTION_RESET_PC                  (OPTION_RESET_PC), // DECODE & DECODE->EXE
    .OPTION_RF_ADDR_WIDTH             (OPTION_RF_ADDR_WIDTH), // DECODE & DECODE->EXE
    .FEATURE_PSYNC                    (FEATURE_PSYNC), // DECODE & DECODE->EXE
    .FEATURE_CSYNC                    (FEATURE_CSYNC) // DECODE & DECODE->EXE
  )
  u_decode
  (
    // INSN
    .dcod_insn_i                      (dcod_insn), // DECODE & DECODE->EXE
    // Data dependancy detection
    .dcod_op_jr_o                     (dcod_op_jr), // DECODE & DECODE->EXE
    .exe2dec_hazard_d1b1_i            (exe2dec_hazard_d1b1), // DECODE & DECODE->EXE
    // PC
    .pc_decode_i                      (pc_decode), // DECODE & DECODE->EXE
    // IMM
    .dcod_immediate_o                 (dcod_immediate), // DECODE & DECODE->EXE
    .dcod_immediate_sel_o             (dcod_immediate_sel), // DECODE & DECODE->EXE
    // various instruction attributes
    .dcod_rfa1_req_o                  (dcod_rfa1_req), // DECODE & DECODE->EXE
    .dcod_rfb1_req_o                  (dcod_rfb1_req), // DECODE & DECODE->EXE
    .dcod_rfd1_wb_o                   (dcod_rfd1_wb), // DECODE & DECODE->EXE
    .dcod_rfd1_adr_o                  (dcod_rfd1_adr), // DECODE & DECODE->EXE
    .dcod_flag_wb_o                   (dcod_flag_wb), // DECODE & DECODE->EXE
    .dcod_carry_wb_o                  (dcod_carry_wb), // DECODE & DECODE->EXE
    .dcod_flag_req_o                  (dcod_flag_req), // DECODE & DECODE->EXE
    .dcod_carry_req_o                 (dcod_carry_req), // DECODE & DECODE->EXE
    // for FPU64
    .dcod_rfa2_req_o                  (dcod_rfa2_req), // DECODE & DECODE->EXE
    .dcod_rfb2_req_o                  (dcod_rfb2_req), // DECODE & DECODE->EXE
    .insn_rfd2_adr_i                  (insn_rfd2_adr), // DECODE & DECODE->EXE
    .dcod_rfd2_adr_o                  (dcod_rfd2_adr), // DECODE & DECODE->EXE
    // flag & branches
    .dcod_jump_or_branch_o            (dcod_jump_or_branch), // DECODE & DECODE->EXE
    // Forwarding comparision flag
    .exec_op_1clk_cmp_i               (exec_op_1clk_cmp), // DECODE & DECODE->EXE
    .exec_flag_set_i                  (exec_flag_set), // DECODE & DECODE->EXE
    .ctrl_flag_i                      (ctrl_flag), // DECODE & DECODE->EXE
    // Do jump/branch and jump/branch target for FETCH
    .dcod_rfb1_jr_i                   (dcod_rfb1_jr), // DECODE & DECODE->EXE
    .dcod_do_branch_o                 (dcod_do_branch), // DECODE & DECODE->EXE
    .dcod_do_branch_target_o          (dcod_do_branch_target), // DECODE & DECODE->EXE
    // Signals to stall FETCH if we are waiting flag
    //  # flag is going to be written by multi-cycle instruction
    //  # like 64-bit FPU comparison or l.swa
    .dcod_flag_wb_mcycle_o            (dcod_flag_wb_mcycle), // DECODE & DECODE->EXE
    //  # conditional branch
    .dcod_op_brcond_o                 (dcod_op_brcond), // DECODE & DECODE->EXE
    // LSU related
    .dcod_imm16_o                     (dcod_imm16), // DECODE & DECODE->EXE
    .dcod_op_lsu_load_o               (dcod_op_lsu_load), // DECODE & DECODE->EXE
    .dcod_op_lsu_store_o              (dcod_op_lsu_store), // DECODE & DECODE->EXE
    .dcod_op_lsu_atomic_o             (dcod_op_lsu_atomic), // DECODE & DECODE->EXE
    .dcod_lsu_length_o                (dcod_lsu_length), // DECODE & DECODE->EXE
    .dcod_lsu_zext_o                  (dcod_lsu_zext), // DECODE & DECODE->EXE
    .dcod_op_msync_o                  (dcod_op_msync), // DECODE & DECODE->EXE
    // Instruction which passes EXECUTION through
    .dcod_op_pass_exec_o              (dcod_op_pass_exec), // DECODE & DECODE->EXE
    // 1-clock instruction
    .dcod_op_1clk_o                   (dcod_op_1clk), // DECODE & DECODE->EXE
    // ALU related opc
    .dcod_opc_alu_secondary_o         (dcod_opc_alu_secondary), // DECODE & DECODE->EXE
    // Adder related
    .dcod_op_add_o                    (dcod_op_add), // DECODE & DECODE->EXE
    .dcod_adder_do_sub_o              (dcod_adder_do_sub), // DECODE & DECODE->EXE
    .dcod_adder_do_carry_o            (dcod_adder_do_carry), // DECODE & DECODE->EXE
    // Various 1-clock related
    .dcod_op_shift_o                  (dcod_op_shift), // DECODE & DECODE->EXE
    .dcod_op_ffl1_o                   (dcod_op_ffl1), // DECODE & DECODE->EXE
    .dcod_op_movhi_o                  (dcod_op_movhi), // DECODE & DECODE->EXE
    .dcod_op_cmov_o                   (dcod_op_cmov), // DECODE & DECODE->EXE
    // Logic
    .dcod_opc_logic_o                 (dcod_opc_logic), // DECODE & DECODE->EXE
    // Jump & Link
    .dcod_op_jal_o                    (dcod_op_jal), // DECODE & DECODE->EXE
    .dcod_jal_result_o                (dcod_jal_result), // DECODE & DECODE->EXE
    // Set flag related
    .dcod_op_setflag_o                (dcod_op_setflag), // DECODE & DECODE->EXE
    .dcod_op_fp32_cmp_o               (dcod_op_fp32_cmp), // DECODE & DECODE->EXE
    .dcod_opc_fp32_cmp_o              (dcod_opc_fp32_cmp), // DECODE & DECODE->EXE
    // Multiplier related
    .dcod_op_mul_o                    (dcod_op_mul), // DECODE & DECODE->EXE
    // Divider related
    .dcod_op_div_o                    (dcod_op_div), // DECODE & DECODE->EXE
    .dcod_op_div_signed_o             (dcod_op_div_signed), // DECODE & DECODE->EXE
    .dcod_op_div_unsigned_o           (dcod_op_div_unsigned), // DECODE & DECODE->EXE
    // FPU-64 arithmetic part
    .dcod_op_fpxx_arith_o             (dcod_op_fpxx_arith), // DECODE & DECODE->EXE
    .dcod_op_fp64_arith_o             (dcod_op_fp64_arith), // DECODE & DECODE->EXE
    .dcod_op_fpxx_add_o               (dcod_op_fpxx_add), // DECODE & DECODE->EXE
    .dcod_op_fpxx_sub_o               (dcod_op_fpxx_sub), // DECODE & DECODE->EXE
    .dcod_op_fpxx_mul_o               (dcod_op_fpxx_mul), // DECODE & DECODE->EXE
    .dcod_op_fpxx_div_o               (dcod_op_fpxx_div), // DECODE & DECODE->EXE
    .dcod_op_fpxx_i2f_o               (dcod_op_fpxx_i2f), // DECODE & DECODE->EXE
    .dcod_op_fpxx_f2i_o               (dcod_op_fpxx_f2i), // DECODE & DECODE->EXE
    // FPU-64 comparison part
    .dcod_op_fp64_cmp_o               (dcod_op_fp64_cmp), // DECODE & DECODE->EXE
    .dcod_opc_fp64_cmp_o              (dcod_opc_fp64_cmp), // DECODE & DECODE->EXE
    // MTSPR / MFSPR
    .dcod_op_mfspr_o                  (dcod_op_mfspr), // DECODE & DECODE->EXE
    .dcod_op_mtspr_o                  (dcod_op_mtspr), // DECODE & DECODE->EXE
    // Exception flags
    //  ## enable l.trap exception
    .du_trap_enable_i                 (du_trap_enable), // DECODE & DECODE->EXE
    //  ## outcome exception flags
    .fetch_except_ibus_align_o        (fetch_except_ibus_align), // DECODE & DECODE->EXE
    .dcod_except_illegal_o            (dcod_except_illegal), // DECODE & DECODE->EXE
    .dcod_except_syscall_o            (dcod_except_syscall), // DECODE & DECODE->EXE
    .dcod_except_trap_o               (dcod_except_trap), // DECODE & DECODE->EXE
    // RFE proc
    .dcod_op_rfe_o                    (dcod_op_rfe) // DECODE & DECODE->EXE
  );


  //-------------------//
  // [O]rder [MAN]ager //
  //-------------------//

  mor1kx_oman_marocchino
  #(
    .OPTION_OPERAND_WIDTH       (OPTION_OPERAND_WIDTH), // OMAN
    .OPTION_RF_ADDR_WIDTH       (OPTION_RF_ADDR_WIDTH), // OMAN
    .DEST_REG_ADDR_WIDTH        (DEST_REG_ADDR_WIDTH), // OMAN
    .DEST_EXT_ADDR_WIDTH        (DEST_EXT_ADDR_WIDTH) // OMAN
  )
  u_oman
  (
    // clock & reset
    .clk                        (clk), // OMAN
    .rst                        (rst), // OMAN

    // pipeline control
    .padv_decode_i              (padv_decode), // OMAN
    .padv_wb_i                  (padv_wb), // OMAN
    .pipeline_flush_i           (pipeline_flush), // OMAN

    // DECODE non-latched flags to indicate next required unit
    // (The information is stored in order control buffer)
    .dcod_op_pass_exec_i        (dcod_op_pass_exec), // OMAN
    .dcod_jump_or_branch_i      (dcod_jump_or_branch), // OMAN
    .dcod_op_1clk_i             (dcod_op_1clk), // OMAN
    .dcod_op_div_i              (dcod_op_div), // OMAN
    .dcod_op_mul_i              (dcod_op_mul), // OMAN
    .dcod_op_fpxx_arith_i       (dcod_op_fpxx_arith), // OMAN
    .dcod_op_ls_i               (dcod_op_lsu_load | dcod_op_lsu_store), // OMAN
    .dcod_op_rfe_i              (dcod_op_rfe), // OMAN
    // for FPU64
    .dcod_op_fp64_arith_i       (dcod_op_fp64_arith), // OMAN
    .dcod_op_fp64_cmp_i         (dcod_op_fp64_cmp), // OMAN

    // DECODE non-latched additional information related instruction
    //  part #1: iformation stored in order control buffer
    .pc_decode_i                (pc_decode), // OMAN
    .dcod_rfd1_adr_i            (dcod_rfd1_adr), // OMAN
    .dcod_rfd1_wb_i             (dcod_rfd1_wb), // OMAN
    .dcod_carry_wb_i            (dcod_carry_wb), // OMAN
    .dcod_flag_wb_mcycle_i      (dcod_flag_wb_mcycle), // OMAN
    .dcod_flag_wb_i             (dcod_flag_wb), // OMAN
    .dcod_delay_slot_i          (dcod_delay_slot), // OMAN
    //            for FPU64
    .dcod_rfd2_adr_i            (dcod_rfd2_adr), // OMAN
    //  part #2: information required for data dependancy detection
    .dcod_rfa1_req_i            (dcod_rfa1_req), // OMAN
    .dcod_rfa1_adr_i            (dcod_rfa1_adr), // OMAN
    .dcod_rfb1_req_i            (dcod_rfb1_req), // OMAN
    .dcod_rfb1_adr_i            (dcod_rfb1_adr), // OMAN
    .dcod_flag_req_i            (dcod_flag_req), // OMAN
    .dcod_carry_req_i           (dcod_carry_req), // OMAN
    .dcod_op_jr_i               (dcod_op_jr), // OMAN
    .dcod_op_brcond_i           (dcod_op_brcond), // OMAN
    .busy_op_1clk_cmp_i         (busy_op_1clk_cmp), // OMAN
    //  part #3: information required for create enable for
    //           for external (timer/ethernet/uart/etc) interrupts
    .dcod_op_lsu_store_i        (dcod_op_lsu_store), // OMAN
    .dcod_op_mtspr_i            (dcod_op_mtspr), // OMAN
    .dcod_op_msync_i            (dcod_op_msync), // OMAN
    //  part #4: for MF(T)SPR processing
    .dcod_op_mfspr_i            (dcod_op_mfspr), // OMAN
    //  part #5: for FPU64, data dependancy detection
    .dcod_rfa2_req_i            (dcod_rfa2_req), // OMAN
    .dcod_rfa2_adr_i            (dcod_rfa2_adr), // OMAN
    .dcod_rfb2_req_i            (dcod_rfb2_req), // OMAN
    .dcod_rfb2_adr_i            (dcod_rfb2_adr), // OMAN

    // collect busy flags from exwcution module
    .op_1clk_busy_i             (op_1clk_busy), // OMAN
    .mclk_busy_i                (mclk_busy), // OMAN
    .lsu_busy_i                 (lsu_busy), // OMAN
    .wb_lsu_valid_miss_i        (wb_lsu_valid_miss), // OMAN
    .wb_rfd1_wb_lsu_miss_i      (wb_rfd1_wb_lsu_miss), // OMAN
    .wb_flag_wb_lsu_miss_i      (wb_flag_wb_lsu_miss), // OMAN

    // collect valid flags from execution modules
    .exec_op_1clk_i             (exec_op_1clk), // OMAN
    .div_valid_i                (div_valid), // OMAN
    .mul_valid_i                (mul_valid), // OMAN
    .fpxx_arith_valid_i         (fpxx_arith_valid), // OMAN
    .exec_op_fp64_cmp_i         (exec_op_fp64_cmp), // OMAN
    .lsu_valid_i                (lsu_valid), // OMAN: result ready or exceptions

    // D1 related WB-to-DECODE hazards for LSU WB miss processing
    .dcod_wb2dec_eq_adr_d1a1_i  (dcod_wb2dec_eq_adr_d1a1), // OMAN
    .dcod_wb2dec_eq_adr_d1b1_i  (dcod_wb2dec_eq_adr_d1b1), // OMAN
    .dcod_wb2dec_eq_adr_d1a2_i  (dcod_wb2dec_eq_adr_d1a2), // OMAN
    .dcod_wb2dec_eq_adr_d1b2_i  (dcod_wb2dec_eq_adr_d1b2), // OMAN
    // D1 relased EXECUTE-to-DECODE hazards for LSU WB miss processing
    .exec_wb2exe_hazard_d1xx_i  (exec_wb2exe_hazard_d1xx_1clk), // OMAN specially for l.bf/l.bnf
    .exec_op_1clk_cmp_i         (exec_op_1clk_cmp), // OMAN specially for l.bf/l.bnf

    // FETCH & DECODE exceptions
    .fetch_except_ibus_err_i    (fetch_except_ibus_err), // OMAN
    .fetch_except_ipagefault_i  (fetch_except_ipagefault), // OMAN
    .fetch_except_itlb_miss_i   (fetch_except_itlb_miss), // OMAN
    .fetch_an_except_i          (fetch_an_except), // OMAN
    .fetch_except_ibus_align_i  (fetch_except_ibus_align), // OMAN
    .dcod_except_illegal_i      (dcod_except_illegal), // OMAN
    .dcod_except_syscall_i      (dcod_except_syscall), // OMAN
    .dcod_except_trap_i         (dcod_except_trap), // OMAN

    // OMAN-to-DECODE hazards
    //  combined flag
    .omn2dec_a_hazard_lsu_o     (omn2dec_a_hazard_lsu), // OMAN
    .omn2dec_a_hazard_1clk_o    (omn2dec_a_hazard_1clk), // OMAN
    .omn2dec_a_hazard_mclk_o    (omn2dec_a_hazard_mclk), // OMAN
    //  by FLAG and CARRY
    .busy_hazard_f_o            (busy_hazard_f), // OMAN
    .busy_hazard_f_adr_o        (busy_hazard_f_adr), // OMAN
    .busy_hazard_c_o            (busy_hazard_c), // OMAN
    .busy_hazard_c_adr_o        (busy_hazard_c_adr), // OMAN
    //  by operands
    .busy_hazard_d1a1_o         (busy_hazard_d1a1), // OMAN
    .busy_hazard_d1a1_adr_o     (busy_hazard_d1a1_adr), // OMAN
    .busy_hazard_d1b1_o         (busy_hazard_d1b1), // OMAN
    .busy_hazard_d1b1_adr_o     (busy_hazard_d1b1_adr), // OMAN
    .busy_hazard_d2a1_o         (busy_hazard_d2a1), // OMAN
    .busy_hazard_d2a1_adr_o     (busy_hazard_d2a1_adr), // OMAN
    .busy_hazard_d2b1_o         (busy_hazard_d2b1), // OMAN
    .busy_hazard_d2b1_adr_o     (busy_hazard_d2b1_adr), // OMAN
    .busy_hazard_d1a2_o         (busy_hazard_d1a2), // OMAN
    .busy_hazard_d1a2_adr_o     (busy_hazard_d1a2_adr), // OMAN
    .busy_hazard_d1b2_o         (busy_hazard_d1b2), // OMAN
    .busy_hazard_d1b2_adr_o     (busy_hazard_d1b2_adr), // OMAN
    .busy_hazard_d2a2_o         (busy_hazard_d2a2), // OMAN
    .busy_hazard_d2a2_adr_o     (busy_hazard_d2a2_adr), // OMAN
    .busy_hazard_d2b2_o         (busy_hazard_d2b2), // OMAN
    .busy_hazard_d2b2_adr_o     (busy_hazard_d2b2_adr), // OMAN

    // EXEC-to-DECODE hazards
    //  combined flag
    .exe2dec_a_hazard_lsu_o     (exe2dec_a_hazard_lsu), // OMAN
    .exe2dec_a_hazard_1clk_o    (exe2dec_a_hazard_1clk), // OMAN
    .exe2dec_a_hazard_mclk_o    (exe2dec_a_hazard_mclk), // OMAN
    //  by operands
    .exe2dec_hazard_d1a1_o      (exe2dec_hazard_d1a1), // OMAN
    .exe2dec_hazard_d1b1_o      (exe2dec_hazard_d1b1), // OMAN
    .exe2dec_hazard_d2a1_o      (exe2dec_hazard_d2a1), // OMAN
    .exe2dec_hazard_d2b1_o      (exe2dec_hazard_d2b1), // OMAN
    .exe2dec_hazard_d1a2_o      (exe2dec_hazard_d1a2), // OMAN
    .exe2dec_hazard_d1b2_o      (exe2dec_hazard_d1b2), // OMAN
    .exe2dec_hazard_d2a2_o      (exe2dec_hazard_d2a2), // OMAN
    .exe2dec_hazard_d2b2_o      (exe2dec_hazard_d2b2), // OMAN
    // Data for resolving hazards by passing from DECODE to EXECUTE
    .exec_flag_wb_o             (exec_flag_wb), // OMAN
    .exec_carry_wb_o            (exec_carry_wb), // OMAN
    .exec_rfd1_wb_o             (exec_rfd1_wb), // OMAN
    .exec_rfd2_wb_o             (exec_rfd2_wb), // OMAN
    .exec_ext_adr_o             (exec_ext_adr), // OMAN

    // Stall fetch by specific type of hazards
    .exec_an_except_o           (exec_an_except), // OMAN
    // Signal to FETCH that target address or flag isn't ready
    .fetch_waiting_target_o     (fetch_waiting_target), // OMAN

    // DECODE result could be processed by EXECUTE
    .dcod_valid_o               (dcod_valid), // OMAN

    // EXECUTE completed (desired unit is ready)
    .exec_valid_o               (exec_valid), // OMAN

    // control WB latches of execution modules
    .grant_wb_to_1clk_o         (grant_wb_to_1clk), // OMAN
    .grant_wb_to_div_o          (grant_wb_to_div), // OMAN
    .grant_wb_to_mul_o          (grant_wb_to_mul), // OMAN
    .grant_wb_to_fpxx_arith_o   (grant_wb_to_fpxx_arith), // OMAN
    .grant_wb_to_lsu_o          (grant_wb_to_lsu), // OMAN
    // for FPU64
    .grant_wb_to_fp64_cmp_o     (grant_wb_to_fp64_cmp), // OMAN

    // Support IBUS error handling in CTRL
    .exec_jump_or_branch_o      (exec_jump_or_branch), // OMAN
    .pc_exec_o                  (pc_exec), // OMAN

    //   Flag to enabel/disable exterlal interrupts processing
    // depending on the fact is instructions restartable or not
    .exec_interrupts_en_o       (exec_interrupts_en), // OMAN

    // WB outputs
    //  ## instruction related information
    .pc_wb_o                    (pc_wb), // OMAN
    .wb_delay_slot_o            (wb_delay_slot), // OMAN
    .wb_rfd1_adr_o              (wb_rfd1_adr[(DEST_REG_ADDR_WIDTH-1):0]), // OMAN
    .wb_rfd1_wb_o               (wb_rfd1_wb), // OMAN
    .wb_flag_wb_o               (wb_flag_wb), // OMAN
    .wb_carry_wb_o              (wb_carry_wb), // OMAN
    // for FPU64
    .wb_rfd2_adr_o              (wb_rfd2_adr), // OMAN
    .wb_rfd2_wb_o               (wb_rfd2_wb), // OMAN
    //  ## RFE processing
    .wb_op_rfe_o                (wb_op_rfe), // OMAN
    //  ## IFETCH exceptions
    .wb_except_ibus_err_o       (wb_except_ibus_err), // OMAN
    .wb_except_ipagefault_o     (wb_except_ipagefault), // OMAN
    .wb_except_itlb_miss_o      (wb_except_itlb_miss), // OMAN
    .wb_except_ibus_align_o     (wb_except_ibus_align), // OMAN
    //  ## DECODE exceptions
    .wb_except_illegal_o        (wb_except_illegal), // OMAN
    .wb_except_syscall_o        (wb_except_syscall), // OMAN
    .wb_except_trap_o           (wb_except_trap), // OMAN
    //  ## combined DECODE/IFETCH exceptions
    .wb_fd_an_except_o          (wb_fd_an_except) // OMAN
  );


  //-----------------------------------------------//
  // 1-clock operations including FP-32 comparison //
  //-----------------------------------------------//

  // single clock operations controls
  //  # opcode for alu
  wire [`OR1K_ALU_OPC_WIDTH-1:0] exec_opc_alu_secondary;
  //  # adder's inputs
  wire                           exec_op_add;
  wire                           exec_adder_do_sub;
  wire                           exec_adder_do_carry;
  //  # shift, ffl1, movhi, cmov
  wire                           exec_op_shift;
  wire                           exec_op_ffl1;
  wire                           exec_op_movhi;
  wire                           exec_op_cmov;
  //  # logic
  wire                           exec_op_logic;
  wire [`OR1K_ALU_OPC_WIDTH-1:0] exec_opc_logic;
  //  # jump & link
  wire                            exec_op_jal;
  wire [OPTION_OPERAND_WIDTH-1:0] exec_jal_result;
  //  # flag related inputs
  wire                           exec_op_setflag;
  wire                           exec_op_fp32_cmp;
  wire                     [2:0] exec_opc_fp32_cmp;

  // attributes include all of earlier components
  localparam ONE_CLK_ATTR_WIDTH = 15 + (2 * `OR1K_ALU_OPC_WIDTH) + OPTION_OPERAND_WIDTH;

  // from BUSY stage of 1-clk reservation station
  wire [ONE_CLK_ATTR_WIDTH-1:0] busy_opc_1clk;

  // input operands A and B with forwarding from WB
  wire [OPTION_OPERAND_WIDTH-1:0] exec_1clk_a1;
  wire [OPTION_OPERAND_WIDTH-1:0] exec_1clk_b1;

  //  # update carry flag by 1clk-operation
  wire wb_1clk_carry_set;
  wire wb_1clk_carry_clear;

  //  # update overflow flag by 1clk-operation
  wire wb_1clk_overflow_set;
  wire wb_1clk_overflow_clear;

  // **** reservation station for 1-clk ****
  mor1kx_rsrvs_marocchino
  #(
    .OPTION_OPERAND_WIDTH         (OPTION_OPERAND_WIDTH), // 1CLK_RSVRS
    .OPC_WIDTH                    (ONE_CLK_ATTR_WIDTH), // 1CLK_RSVRS
    .DEST_EXT_ADDR_WIDTH          (DEST_EXT_ADDR_WIDTH), // 1CLK_RSVRS
    // Reservation station is used at input of modules:
    //  1CLK: only parameter RSRVS-1CLK must be set to "1"
    //  MCLK: only parameter RSRVS-MCLK must be set to "1"
    //  LSU : RSRVS-1CLK and RSRVS-MCLK parameters must be set to "0"
    .RSRVS_1CLK                   (1), // 1CLK_RSVRS
    .RSRVS_MCLK                   (0), // 1CLK_RSVRS
    // Packed operands for various reservation stations:
    //  # LSU : {   x,    x, rfb1, rfa1}
    //  # 1CLK: {   x,    x, rfb1, rfa1}
    //  # MCLK: {rfb2, rfa2, rfb1, rfa1}
    .DCOD_RFXX_WIDTH              (2 * OPTION_OPERAND_WIDTH), // 1CLK_RSRVS
    // OMAN-to-DECODE hazards layout for various reservation stations:
    //  # LSU : {   x,    x,    x,    x, d2b1, d2a1, d1b1, d1a1 }
    //  # 1CLK: {   x,    x, carr, flag, d2b1, d2a1, d1b1, d1a1 }
    //  # MCLK: {d2b2, d2a2, d1b2, d1a2, d2b1, d2a1, d1b1, d1a1 }
    .BUSY_HAZARDS_FLAGS_WIDTH     (6), // 1CLK_RSVRS
    .BUSY_HAZARDS_ADDRS_WIDTH     (6 * DEST_EXT_ADDR_WIDTH), // 1CLK_RSVRS
    // BUSY-to-EXECUTE pass hazards data layout for various reservation stations:
    // (it is also layout for WB-resolving hazards)
    //  # LSU : {    x,     x, d2_wr, d1_wr, ext_bits }
    //  # 1CLK: { carr,  flag, d2_wr, d1_wr, ext_bits }
    //  # MCLK: {    x,     x, d2_wr, d1_wr, ext_bits }
    .BUSY2EXEC_PASS_DATA_WIDTH    (4 + DEST_EXT_ADDR_WIDTH), // 1CLK_RSVRS
    // EXEC-to-DECODE hazards layout for various reservation stations:
    //  # LSU : {   x,    x,    x,    x, d2b1, d2a1, d1b1, d1a1 }
    //  # 1CLK: {   x,    x,    x,    x, d2b1, d2a1, d1b1, d1a1 }
    //  # MCLK: {d2b2, d2a2, d1b2, d1a2, d2b1, d2a1, d1b1, d1a1 }
    .EXE2DEC_HAZARDS_FLAGS_WIDTH  (4) // 1CLK_RSVRS
  )
  u_1clk_rsrvs
  (
    // clocks and resets
    .clk                        (clk), // 1CLK_RSVRS
    .rst                        (rst), // 1CLK_RSVRS
    // pipeline control signals in
    .pipeline_flush_i           (pipeline_flush), // 1CLK_RSVRS
    .padv_decode_i              (padv_decode), // 1CLK_RSVRS
    .taking_op_i                (padv_wb & grant_wb_to_1clk), // 1CLK_RSVRS
    // input data from DECODE
    .dcod_rfxx_i                ({dcod_rfb1, dcod_rfa1}), // 1CLK_RSVRS
    // OMAN-to-DECODE hazards
    //  combined flag
    .omn2dec_a_hazard_i         (omn2dec_a_hazard_1clk), // 1CLK_RSVRS
    //  # hazards flags
    .busy_hazards_flags_i       ({busy_hazard_c,    busy_hazard_f, // 1CLK_RSVRS
                                  busy_hazard_d2b1, busy_hazard_d2a1, // 1CLK_RSVRS
                                  busy_hazard_d1b1, busy_hazard_d1a1}), // 1CLK_RSVRS
    //  # hasards addresses
    .busy_hazards_addrs_i       ({busy_hazard_c_adr,    busy_hazard_f_adr, // 1CLK_RSVRS
                                  busy_hazard_d2b1_adr, busy_hazard_d2a1_adr, // 1CLK_RSVRS
                                  busy_hazard_d1b1_adr, busy_hazard_d1a1_adr}), // 1CLK_RSVRS
    // EXEC-to-DECODE hazards
    //  combined flag
    .exe2dec_a_hazard_i         (exe2dec_a_hazard_1clk), // 1CLK_RSVRS
    //  hazards flags
    .exe2dec_hazards_flags_i    ({exe2dec_hazard_d2b1, exe2dec_hazard_d2a1, // 1CLK_RSVRS
                                  exe2dec_hazard_d1b1, exe2dec_hazard_d1a1}), // 1CLK_RSVRS
    // Hazard could be passed from DECODE to EXECUTE
    //  ## packed input
    .busy2exec_pass_data_i      ({exec_carry_wb, exec_flag_wb, // 1CLK_RSVRS
                                  exec_rfd2_wb,  exec_rfd1_wb, exec_ext_adr}), // 1CLK_RSVRS
    //  ## passing only with writting back
    .padv_wb_i                  (padv_wb), // 1CLK_RSVRS
    // Hazard could be resolving
    //  ## packed input
    .wb2exe_hazards_data_i      ({wb_carry_wb, wb_flag_wb, // 1CLK_RSVRS
                                  wb_rfd2_wb,  wb_rfd1_wb, // 1CLK_RSVRS
                                  wb_rfd1_adr[(DEST_REG_ADDR_WIDTH-1):OPTION_RF_ADDR_WIDTH]}), // 1CLK_RSVRS
    //  ## forwarding results
    .wb_result1_i               (wb_result1), // 1CLK_RSVRS
    .wb_result2_i               (wb_result2), // 1CLK_RSVRS
    // Processing of LSU's WB-miss
    .wb_rfd1_wb_lsu_miss_i      (wb_rfd1_wb_lsu_miss), // 1CLK_RSVRS
    // command and its additional attributes
    .dcod_op_i                  (dcod_op_1clk), // 1CLK_RSVRS
    .dcod_opc_i                 ({dcod_opc_alu_secondary, // 1CLK_RSVRS
                                  dcod_op_add, dcod_adder_do_sub, dcod_adder_do_carry, // 1CLK_RSVRS
                                  dcod_op_shift, dcod_op_ffl1, dcod_op_movhi, dcod_op_cmov, // 1CLK_RSVRS
                                  (|dcod_opc_logic), dcod_opc_logic, // 1CLK_RSVRS
                                  dcod_op_jal, dcod_jal_result, // 1CLK_RSVRS
                                  dcod_op_setflag, dcod_op_fp32_cmp, dcod_opc_fp32_cmp, // 1CLK_RSVRS
                                  (dcod_op_setflag | dcod_op_fp32_cmp)}), // 1CLK_RSVRS
    //   command attributes from busy stage
    .busy_opc_o                 (busy_opc_1clk), // 1CLK_RSVRS
    //   combined D1XX hazards
    .exec_wb2exe_hazard_d1xx_o  (exec_wb2exe_hazard_d1xx_1clk), // 1CLK_RSVRS
    // outputs
    //   command and its additional attributes
    .exec_op_o                  (exec_op_1clk), // 1CLK_RSVRS
    .exec_opc_o                 ({exec_opc_alu_secondary, // 1CLK_RSVRS
                                  exec_op_add, exec_adder_do_sub, exec_adder_do_carry, // 1CLK_RSVRS
                                  exec_op_shift, exec_op_ffl1, exec_op_movhi, exec_op_cmov, // 1CLK_RSVRS
                                  exec_op_logic, exec_opc_logic, // 1CLK_RSVRS
                                  exec_op_jal, exec_jal_result, // 1CLK_RSVRS
                                  exec_op_setflag, exec_op_fp32_cmp, exec_opc_fp32_cmp, // 1CLK_RSVRS
                                  exec_op_1clk_cmp}), // 1CLK_RSVRS
    //   operands
    .exec_rfa1_o                (exec_1clk_a1), // 1CLK_RSVRS
    .exec_rfb1_o                (exec_1clk_b1), // 1CLK_RSVRS
    //  ## for FPU64
    .exec_rfa2_o                (), // 1CLK_RSVRS
    .exec_rfb2_o                (), // 1CLK_RSVRS
    //   unit-is-busy flag
    .unit_busy_o                (op_1clk_busy) // 1CLK_RSVRS
  );

  // to OMAN for hazards detection
  assign busy_op_1clk_cmp = busy_opc_1clk[0];

  // **** 1clk ****
  mor1kx_exec_1clk_marocchino
  #(
    .OPTION_OPERAND_WIDTH             (OPTION_OPERAND_WIDTH) // 1CLK
  )
  u_exec_1clk
  (
    // clocks & resets
    .clk                              (clk), // 1CLK
    .rst                              (rst), // 1CLK

    // pipeline controls
    .pipeline_flush_i                 (pipeline_flush), // 1CLK
    .padv_wb_i                        (padv_wb), // 1CLK
    .grant_wb_to_1clk_i               (grant_wb_to_1clk), // 1CLK

    // input operands A and B with forwarding from WB
    .exec_1clk_a1_i                   (exec_1clk_a1), // 1CLK
    .exec_1clk_b1_i                   (exec_1clk_b1), // 1CLK

    // 1-clock instruction auxiliaries
    .exec_opc_alu_secondary_i         (exec_opc_alu_secondary), // 1CLK
    .carry_i                          (ctrl_carry), // 1CLK
    .flag_i                           (ctrl_flag), // 1CLK

    // adder
    .exec_op_add_i                    (exec_op_add), // 1CLK
    .exec_adder_do_sub_i              (exec_adder_do_sub), // 1CLK
    .exec_adder_do_carry_i            (exec_adder_do_carry), // 1CLK
    // shift, ffl1, movhi, cmov
    .exec_op_shift_i                  (exec_op_shift), // 1CLK
    .exec_op_ffl1_i                   (exec_op_ffl1), // 1CLK
    .exec_op_movhi_i                  (exec_op_movhi), // 1CLK
    .exec_op_cmov_i                   (exec_op_cmov), // 1CLK
    // logic
    .exec_op_logic_i                  (exec_op_logic), // 1CLK
    .exec_opc_logic_i                 (exec_opc_logic), // 1CLK
    // jump & link
    .exec_op_jal_i                    (exec_op_jal), // 1CLK
    .exec_jal_result_i                (exec_jal_result), // 1CLK
    // WB-latched 1-clock arithmetic result
    .wb_alu_1clk_result_o             (wb_alu_1clk_result), // 1CLK
    //  # update carry flag by 1clk-operation
    .wb_1clk_carry_set_o              (wb_1clk_carry_set), // 1CLK
    .wb_1clk_carry_clear_o            (wb_1clk_carry_clear), // 1CLK
    //  # update overflow flag by 1clk-operation
    .wb_1clk_overflow_set_o           (wb_1clk_overflow_set), // 1CLK
    .wb_1clk_overflow_clear_o         (wb_1clk_overflow_clear), // 1CLK
    //  # generate overflow exception by 1clk-operation
    .except_overflow_enable_i         (except_overflow_enable), // 1CLK
    .wb_except_overflow_1clk_o        (wb_except_overflow_1clk), // 1CLK

    // integer comparison flag
    .exec_op_setflag_i                (exec_op_setflag), // 1CLK
    // WB: integer comparison result
    .wb_int_flag_set_o                (wb_int_flag_set), // 1CLK
    .wb_int_flag_clear_o              (wb_int_flag_clear), // 1CLK

    // FP32 comparison flag
    .exec_op_fp32_cmp_i               (exec_op_fp32_cmp), // 1CLK
    .exec_opc_fp32_cmp_i              (exec_opc_fp32_cmp), // 1CLK
    .except_fpu_enable_i              (except_fpu_enable), // 1CLK
    .ctrl_fpu_mask_flags_inv_i        (ctrl_fpu_mask_flags[`OR1K_FPCSR_IVF - `OR1K_FPCSR_OVF]), // 1CLK
    .ctrl_fpu_mask_flags_inf_i        (ctrl_fpu_mask_flags[`OR1K_FPCSR_INF - `OR1K_FPCSR_OVF]), // 1CLK
    // WB: FP32 comparison results
    .wb_fp32_flag_set_o               (wb_fp32_flag_set), // 1CLK
    .wb_fp32_flag_clear_o             (wb_fp32_flag_clear), // 1CLK
    .wb_fp32_cmp_inv_o                (wb_fp32_cmp_inv), // 1CLK
    .wb_fp32_cmp_inf_o                (wb_fp32_cmp_inf), // 1CLK
    .wb_fp32_cmp_wb_fpcsr_o           (wb_fp32_cmp_wb_fpcsr), // 1CLK
    .wb_except_fp32_cmp_o             (wb_except_fp32_cmp), // 1CLK

    // Forwarding comparision flag result for conditional branch take/not
    .exec_flag_set_o                  (exec_flag_set) // 1CLK
  );


  //---------------------------------------------//
  // Common reservation station for Multi-clokcs //
  // (_mclk) execution modules:                  //
  //   # 32-bits integer multiplier              //
  //   # 32-bits integer divider                 //
  //   # 32/64-bits FP arithmetic                //
  //   # 64-bits FP comparison                   //
  //---------------------------------------------//
  // run integer multiplier
  wire exec_op_mul;
  // run divider
  wire exec_op_div;
  wire exec_op_div_signed;
  wire exec_op_div_unsigned;
  // run fp3264 arithmetic
  wire exec_op_fp64_arith, exec_op_fpxx_add, exec_op_fpxx_sub, exec_op_fpxx_mul,
                           exec_op_fpxx_div, exec_op_fpxx_i2f, exec_op_fpxx_f2i;

  // run fp64 comparison
  //(declared earlier)

  // OPC layout for multi-clocks rezervation station
  //  # run int multiplier:                                     1
  //  # run int divider (+signed, +unsigned):                   3
  //  # double precision bit:                                   1
  //  # fp3264 arithmetic command (add,sub,mul,div,i2f,f2i):    6
  //  # fp64 comparison command:                                1
  //  # fp64 comparison variant:                                3
  //  # ---------------------------------------------------------
  //  # overall:                                               15
  localparam MCLK_OPC_WIDTH = 15;

  // mclk input operands
  wire [(OPTION_OPERAND_WIDTH-1):0] exec_mclk_a1, exec_mclk_a2, exec_mclk_b1, exec_mclk_b2;

  //  # MCLK is tacking operands
  wire imul_taking_op, idiv_taking_op, fpxx_taking_op;
  wire mclk_taking_op = imul_taking_op | idiv_taking_op | fpxx_taking_op;

  // **** mclk reservation station instance ****
  mor1kx_rsrvs_marocchino
  #(
    .OPTION_OPERAND_WIDTH         (OPTION_OPERAND_WIDTH), // MCLK_RSVRS
    .OPC_WIDTH                    (MCLK_OPC_WIDTH), // MCLK_RSVRS
    .DEST_EXT_ADDR_WIDTH          (DEST_EXT_ADDR_WIDTH), // MCLK_RSVRS
    // Reservation station is used at input of modules:
    //  1CLK: only parameter RSRVS-1CLK must be set to "1"
    //  MCLK: only parameter RSRVS-MCLK must be set to "1"
    //  LSU : RSRVS-1CLK and RSRVS-MCLK parameters must be set to "0"
    .RSRVS_1CLK                   (0), // MCLK_RSVRS
    .RSRVS_MCLK                   (1), // MCLK_RSVRS
    // Packed operands for various reservation stations:
    //  # LSU : {   x,    x, rfb1, rfa1}
    //  # 1CLK: {   x,    x, rfb1, rfa1}
    //  # MCLK: {rfb2, rfa2, rfb1, rfa1}
    .DCOD_RFXX_WIDTH              (4 * OPTION_OPERAND_WIDTH), // MCLK_RSRVS
    // OMAN-to-DECODE hazards layout for various reservation stations:
    //  # LSU : {   x,    x,    x,    x, d2b1, d2a1, d1b1, d1a1 }
    //  # 1CLK: {   x,    x, carr, flag, d2b1, d2a1, d1b1, d1a1 }
    //  # MCLK: {d2b2, d2a2, d1b2, d1a2, d2b1, d2a1, d1b1, d1a1 }
    .BUSY_HAZARDS_FLAGS_WIDTH     (8), // MCLK_RSVRS
    .BUSY_HAZARDS_ADDRS_WIDTH     (8 * DEST_EXT_ADDR_WIDTH), // MCLK_RSVRS
    // BUSY-to-EXECUTE pass hazards data layout for various reservation stations:
    // (it is also layout for WB-resolving hazards)
    //  # LSU : {    x,     x, d2_wr, d1_wr, ext_bits }
    //  # 1CLK: { carr,  flag, d2_wr, d1_wr, ext_bits }
    //  # MCLK: {    x,     x, d2_wr, d1_wr, ext_bits }
    .BUSY2EXEC_PASS_DATA_WIDTH    (2 + DEST_EXT_ADDR_WIDTH), // MCLK_RSVRS
    // EXEC-to-DECODE hazards layout for various reservation stations:
    //  # LSU : {   x,    x,    x,    x, d2b1, d2a1, d1b1, d1a1 }
    //  # 1CLK: {   x,    x,    x,    x, d2b1, d2a1, d1b1, d1a1 }
    //  # MCLK: {d2b2, d2a2, d1b2, d1a2, d2b1, d2a1, d1b1, d1a1 }
    .EXE2DEC_HAZARDS_FLAGS_WIDTH  (8) // MCLK_RSVRS
  )
  u_mclk_rsrvs
  (
    // clocks and resets
    .clk                        (clk), // MCLK_RSVRS
    .rst                        (rst), // MCLK_RSVRS
    // pipeline control signals in
    .pipeline_flush_i           (pipeline_flush), // MCLK_RSVRS
    .padv_decode_i              (padv_decode), // MCLK_RSVRS
    .taking_op_i                (mclk_taking_op), // MCLK_RSVRS
    // input data from DECODE
    .dcod_rfxx_i                ({dcod_rfb2, dcod_rfa2, dcod_rfb1, dcod_rfa1}), // MCLK_RSVRS
    // OMAN-to-DECODE hazards
    //  combined flag
    .omn2dec_a_hazard_i         (omn2dec_a_hazard_mclk), // MCLK_RSVRS
    //  # hazards flags
    .busy_hazards_flags_i       ({busy_hazard_d2b2, busy_hazard_d2a2, // MCLK_RSVRS
                                  busy_hazard_d1b2, busy_hazard_d1a2, // MCLK_RSVRS
                                  busy_hazard_d2b1, busy_hazard_d2a1, // MCLK_RSVRS
                                  busy_hazard_d1b1, busy_hazard_d1a1}), // MCLK_RSVRS
    //  # hasards addresses
    .busy_hazards_addrs_i       ({busy_hazard_d2b2_adr, busy_hazard_d2a2_adr, // MCLK_RSVRS
                                  busy_hazard_d1b2_adr, busy_hazard_d1a2_adr, // MCLK_RSVRS
                                  busy_hazard_d2b1_adr, busy_hazard_d2a1_adr, // MCLK_RSVRS
                                  busy_hazard_d1b1_adr, busy_hazard_d1a1_adr}), // MCLK_RSVRS
    // EXEC-to-DECODE hazards
    //  combined flag
    .exe2dec_a_hazard_i         (exe2dec_a_hazard_mclk), // MCLK_RSVRS
    //  hazards flags
    .exe2dec_hazards_flags_i    ({exe2dec_hazard_d2b2, exe2dec_hazard_d2a2, // MCLK_RSVRS
                                  exe2dec_hazard_d1b2, exe2dec_hazard_d1a2, // MCLK_RSVRS
                                  exe2dec_hazard_d2b1, exe2dec_hazard_d2a1, // MCLK_RSVRS
                                  exe2dec_hazard_d1b1, exe2dec_hazard_d1a1}), // MCLK_RSVRS
    // Hazard could be passed from DECODE to EXECUTE
    //  ## packed input
    .busy2exec_pass_data_i      ({exec_rfd2_wb, exec_rfd1_wb, exec_ext_adr}), // MCLK_RSVRS
    //  ## passing only with writting back
    .padv_wb_i                  (padv_wb), // MCLK_RSVRS
    // Hazard could be resolving
    //  ## packed input
    .wb2exe_hazards_data_i      ({wb_rfd2_wb, wb_rfd1_wb, // MCLK_RSVRS
                                  wb_rfd1_adr[(DEST_REG_ADDR_WIDTH-1):OPTION_RF_ADDR_WIDTH]}), // MCLK_RSVRS
    //  ## forwarding results
    .wb_result1_i               (wb_result1), // MCLK_RSVRS
    .wb_result2_i               (wb_result2), // MCLK_RSVRS
    // Processing of LSU's WB-miss
    .wb_rfd1_wb_lsu_miss_i      (wb_rfd1_wb_lsu_miss), // MCLK_RSVRS
    // command and its additional attributes
    .dcod_op_i                  (dcod_op_mul | dcod_op_div | dcod_op_fpxx_arith | dcod_op_fp64_cmp), // MCLK_RSVRS
    .dcod_opc_i                 ({dcod_op_mul,  // MCLK_RSVRS
                                  dcod_op_div, dcod_op_div_signed, dcod_op_div_unsigned, // MCLK_RSVRS
                                  dcod_op_fp64_arith, // MCLK_RSVRS
                                  dcod_op_fpxx_add, dcod_op_fpxx_sub, dcod_op_fpxx_mul, // MCLK_RSVRS
                                  dcod_op_fpxx_div, dcod_op_fpxx_i2f, dcod_op_fpxx_f2i, // MCLK_RSVRS
                                  dcod_op_fp64_cmp, dcod_opc_fp64_cmp}), // MCLK_RSVRS
    // outputs
    //   command attributes from busy stage
    .busy_opc_o                 (), // MCLK_RSVRS
    //   combined D1XX hazards
    .exec_wb2exe_hazard_d1xx_o  (), // MCLK_RSVRS
    //   command and its additional attributes
    .exec_op_o                  (), // MCLK_RSVRS
    .exec_opc_o                 ({exec_op_mul, // MCLK_RSVRS
                                  exec_op_div, exec_op_div_signed, exec_op_div_unsigned, // MCLK_RSVRS
                                  exec_op_fp64_arith, // MCLK_RSVRS
                                  exec_op_fpxx_add, exec_op_fpxx_sub, exec_op_fpxx_mul, // MCLK_RSVRS
                                  exec_op_fpxx_div, exec_op_fpxx_i2f, exec_op_fpxx_f2i, // MCLK_RSVRS
                                  exec_op_fp64_cmp, exec_opc_fp64_cmp}), // MCLK_RSVRS
    //   operands
    .exec_rfa1_o                (exec_mclk_a1), // MCLK_RSVRS
    .exec_rfb1_o                (exec_mclk_b1), // MCLK_RSVRS
    .exec_rfa2_o                (exec_mclk_a2), // MCLK_RSVRS
    .exec_rfb2_o                (exec_mclk_b2), // MCLK_RSVRS
    //   unit-is-busy flag
    .unit_busy_o                (mclk_busy) // MCLK_RSVRS
  );


  //-------------------//
  // 32-bit multiplier //
  //-------------------//

  mor1kx_multiplier_marocchino
  #(
    .OPTION_OPERAND_WIDTH             (OPTION_OPERAND_WIDTH) // MUL
  )
  u_multiplier
  (
    // clocks & resets
    .clk                              (clk), // MUL
    .rst                              (rst), // MUL
    // pipeline controls
    .pipeline_flush_i                 (pipeline_flush), // MUL
    .padv_wb_i                        (padv_wb), // MUL
    .grant_wb_to_mul_i                (grant_wb_to_mul), // MUL
    // input operands from reservation station
    .exec_mul_a1_i                    (exec_mclk_a1), // MUL
    .exec_mul_b1_i                    (exec_mclk_b1), // MUL
    //  other inputs/outputs
    .exec_op_mul_i                    (exec_op_mul), // MUL
    .imul_taking_op_o                 (imul_taking_op), // MUL
    .mul_valid_o                      (mul_valid), // MUL
    .wb_mul_result_o                  (wb_mul_result) // MUL
  );


  //----------------//
  // 32-bit divider //
  //----------------//

  //  # update carry flag by division
  wire wb_div_carry_set;
  wire wb_div_carry_clear;

  //  # update overflow flag by division
  wire wb_div_overflow_set;
  wire wb_div_overflow_clear;

  // **** integer divider ****
  mor1kx_divider_marocchino
  #(
    .OPTION_OPERAND_WIDTH             (OPTION_OPERAND_WIDTH) // DIV
  )
  u_divider
  (
    // clocks & resets
    .clk                              (clk), // DIV
    .rst                              (rst), // DIV
    // pipeline controls
    .pipeline_flush_i                 (pipeline_flush), // DIV
    .padv_wb_i                        (padv_wb), // DIV
    .grant_wb_to_div_i                (grant_wb_to_div), // DIV
    // input data from reservation station
    .exec_div_a1_i                    (exec_mclk_a1), // DIV
    .exec_div_b1_i                    (exec_mclk_b1), // DIV
    // division command
    .exec_op_div_i                    (exec_op_div), // DIV
    .exec_op_div_signed_i             (exec_op_div_signed), // DIV
    .exec_op_div_unsigned_i           (exec_op_div_unsigned), // DIV
    // division engine state
    .idiv_taking_op_o                 (idiv_taking_op), // DIV
    .div_valid_o                      (div_valid), // DIV
    // write back
    //  # update carry flag by division
    .wb_div_carry_set_o               (wb_div_carry_set), // DIV
    .wb_div_carry_clear_o             (wb_div_carry_clear), // DIV
    //  # update overflow flag by division
    .wb_div_overflow_set_o            (wb_div_overflow_set), // DIV
    .wb_div_overflow_clear_o          (wb_div_overflow_clear), // DIV
    //  # generate overflow exception by division
    .except_overflow_enable_i         (except_overflow_enable), // DIV
    .wb_except_overflow_div_o         (wb_except_overflow_div), // DIV
    //  # division result
    .wb_div_result_o                  (wb_div_result) // DIV
  );


  //---------//
  // FPU3264 //
  //---------//
  pfpu_top_marocchino  u_pfpu3264
  (
    // clock & reset
    .clk                        (clk), // FPU3264
    .rst                        (rst), // FPU3264

    // pipeline control
    .pipeline_flush_i           (pipeline_flush), // FPU3264
    .padv_wb_i                  (padv_wb), // FPU3264
    .grant_wb_to_fpxx_arith_i   (grant_wb_to_fpxx_arith), // FPU3264
    .grant_wb_to_fp64_cmp_i     (grant_wb_to_fp64_cmp), // FPU3264

    // pipeline control outputs
    .fpxx_taking_op_o           (fpxx_taking_op), // FPU3264
    .fpxx_arith_valid_o         (fpxx_arith_valid), // FPU3264

    // Configuration
    .round_mode_i               (ctrl_fpu_round_mode), // FPU3264
    .except_fpu_enable_i        (except_fpu_enable), // FPU3264
    .ctrl_fpu_mask_flags_i      (ctrl_fpu_mask_flags), // FPU3264

    // Commands for arithmetic part
    .exec_op_fp64_arith_i       (exec_op_fp64_arith), // FPU3264
    .exec_op_fpxx_add_i         (exec_op_fpxx_add), // FPU3264
    .exec_op_fpxx_sub_i         (exec_op_fpxx_sub), // FPU3264
    .exec_op_fpxx_mul_i         (exec_op_fpxx_mul), // FPU3264
    .exec_op_fpxx_div_i         (exec_op_fpxx_div), // FPU3264
    .exec_op_fpxx_i2f_i         (exec_op_fpxx_i2f), // FPU3264
    .exec_op_fpxx_f2i_i         (exec_op_fpxx_f2i), // FPU3264

    // Commands for comparison part
    .exec_opc_fp64_cmp_i        (exec_opc_fp64_cmp), // FPU3264

    // Operands from reservation station
    .exec_fpxx_a1_i             (exec_mclk_a1), // FPU3264
    .exec_fpxx_b1_i             (exec_mclk_b1), // FPU3264
    .exec_fpxx_a2_i             (exec_mclk_a2), // FPU3264
    .exec_fpxx_b2_i             (exec_mclk_b2), // FPU3264

    // FPU2364 arithmetic part
    .wb_fpxx_arith_res_hi_o     (wb_fpxx_arith_res_hi), // FPU3264
    .wb_fpxx_arith_res_lo_o     (wb_fpxx_arith_res_lo), // FPU3264
    .wb_fpxx_arith_fpcsr_o      (wb_fpxx_arith_fpcsr), // FPU3264
    .wb_fpxx_arith_wb_fpcsr_o   (wb_fpxx_arith_wb_fpcsr), // FPU3264
    .wb_except_fpxx_arith_o     (wb_except_fpxx_arith), // FPU3264

    // FPU-64 comparison part
    .wb_fp64_flag_set_o         (wb_fp64_flag_set), // FPU3264
    .wb_fp64_flag_clear_o       (wb_fp64_flag_clear), // FPU3264
    .wb_fp64_cmp_inv_o          (wb_fp64_cmp_inv), // FPU3264
    .wb_fp64_cmp_inf_o          (wb_fp64_cmp_inf), // FPU3264
    .wb_fp64_cmp_wb_fpcsr_o     (wb_fp64_cmp_wb_fpcsr), // FPU3264
    .wb_except_fp64_cmp_o       (wb_except_fp64_cmp) // FPU3264
  );


  //--------------//
  // LSU instance //
  //--------------//

  //  # various LSU <-> RSRVS connections
  wire lsu_taking_op;

  // RSRVS -> LSU connections
  //  # commands
  wire                            exec_op_lsu_load;
  wire                            exec_op_lsu_store;
  wire                            exec_op_lsu_atomic;
  wire                      [1:0] exec_lsu_length;
  wire                            exec_lsu_zext;
  wire                            exec_op_msync;
  //  # immediate offset for address computation
  wire      [`OR1K_IMM_WIDTH-1:0] exec_lsu_imm16;
  //  # PC for store buffer EPCR computation
  wire [OPTION_OPERAND_WIDTH-1:0] exec_sbuf_epcr;
  //  # operands after frorwarding from WB
  wire [OPTION_OPERAND_WIDTH-1:0] exec_lsu_a1;
  wire [OPTION_OPERAND_WIDTH-1:0] exec_lsu_b1;

  // **** reservation station for LSU ****
  // EPCR for store buffer
  //  ## delay-slot ? (pc-4) : pc
  wire [(OPTION_OPERAND_WIDTH-1):0] dcod_sbuf_epcr = pc_decode - {{(OPTION_OPERAND_WIDTH-3){1'b0}},dcod_delay_slot,2'b00};

  // attributes include:
  //  ## separate load, store and atomic flags: averall 3
  //  ## length:            2
  //  ## zero extension:    1
  //  ## l.msync:           1
  //  ## immediate width:  16
  //  ## PC address width: 32
  localparam LSU_ATTR_WIDTH = 7 + `OR1K_IMM_WIDTH + OPTION_OPERAND_WIDTH;

  // reservation station instance
  mor1kx_rsrvs_marocchino
  #(
    .OPTION_OPERAND_WIDTH         (OPTION_OPERAND_WIDTH), // LSU_RSRVS
    .OPC_WIDTH                    (LSU_ATTR_WIDTH), // LSU_RSRVS
    .DEST_EXT_ADDR_WIDTH          (DEST_EXT_ADDR_WIDTH), // LSU_RSRVS
    // Reservation station is used at input of modules:
    //  1CLK: only parameter RSRVS-1CLK must be set to "1"
    //  MCLK: only parameter RSRVS-MCLK must be set to "1"
    //  LSU : RSRVS-1CLK and RSRVS-MCLK parameters must be set to "0"
    .RSRVS_1CLK                   (0), // LSU_RSRVS
    .RSRVS_MCLK                   (0), // LSU_RSRVS
    // Packed operands for various reservation stations:
    //  # LSU : {   x,    x, rfb1, rfa1}
    //  # 1CLK: {   x,    x, rfb1, rfa1}
    //  # MCLK: {rfb2, rfa2, rfb1, rfa1}
    .DCOD_RFXX_WIDTH              (2 * OPTION_OPERAND_WIDTH), // LSU_RSRVS
    // OMAN-to-DECODE hazards layout for various reservation stations:
    //  # LSU : {   x,    x,    x,    x, d2b1, d2a1, d1b1, d1a1 }
    //  # 1CLK: {   x,    x, carr, flag, d2b1, d2a1, d1b1, d1a1 }
    //  # MCLK: {d2b2, d2a2, d1b2, d1a2, d2b1, d2a1, d1b1, d1a1 }
    .BUSY_HAZARDS_FLAGS_WIDTH     (4), // LSU_RSRVS
    .BUSY_HAZARDS_ADDRS_WIDTH     (4 * DEST_EXT_ADDR_WIDTH), // LSU_RSRVS
    // BUSY-to-EXECUTE pass hazards data layout for various reservation stations:
    // (it is also layout for WB-resolving hazards)
    //  # LSU : {    x,     x, d2_wr, d1_wr, ext_bits }
    //  # 1CLK: { carr,  flag, d2_wr, d1_wr, ext_bits }
    //  # MCLK: {    x,     x, d2_wr, d1_wr, ext_bits }
    .BUSY2EXEC_PASS_DATA_WIDTH    (2 + DEST_EXT_ADDR_WIDTH), // LSU_RSRVS
    // EXEC-to-DECODE hazards layout for various reservation stations:
    //  # LSU : {   x,    x,    x,    x, d2b1, d2a1, d1b1, d1a1 }
    //  # 1CLK: {   x,    x,    x,    x, d2b1, d2a1, d1b1, d1a1 }
    //  # MCLK: {d2b2, d2a2, d1b2, d1a2, d2b1, d2a1, d1b1, d1a1 }
    .EXE2DEC_HAZARDS_FLAGS_WIDTH  (4) // LSU_RSRVS
  )
  u_lsu_rsrvs
  (
    // clocks and resets
    .clk                        (clk),
    .rst                        (rst),
    // pipeline control signals in
    .pipeline_flush_i           (pipeline_flush), // LSU_RSVRS
    .padv_decode_i              (padv_decode), // LSU_RSVRS
    .taking_op_i                (lsu_taking_op), // LSU_RSVRS
    // input data from DECODE
    .dcod_rfxx_i                ({dcod_rfb1, dcod_rfa1}), // LSU_RSVRS
    // OMAN-to-DECODE hazards
    //  combined flag
    .omn2dec_a_hazard_i         (omn2dec_a_hazard_lsu), // LSU_RSVRS
    //  # hazards flags
    .busy_hazards_flags_i       ({busy_hazard_d2b1, busy_hazard_d2a1, // LSU_RSVRS
                                  busy_hazard_d1b1, busy_hazard_d1a1}), // LSU_RSVRS
    //  # hasards addresses
    .busy_hazards_addrs_i       ({busy_hazard_d2b1_adr, busy_hazard_d2a1_adr, // LSU_RSVRS
                                  busy_hazard_d1b1_adr, busy_hazard_d1a1_adr}), // LSU_RSVRS
    // EXEC-to-DECODE hazards
    //  combined flag
    .exe2dec_a_hazard_i         (exe2dec_a_hazard_lsu), // LSU_RSVRS
    //  hazards flags
    .exe2dec_hazards_flags_i    ({exe2dec_hazard_d2b1, exe2dec_hazard_d2a1, // LSU_RSVRS
                                  exe2dec_hazard_d1b1, exe2dec_hazard_d1a1}), // LSU_RSVRS
    // Hazard could be passed from DECODE to EXECUTE
    //  ## packed input
    .busy2exec_pass_data_i      ({exec_rfd2_wb, exec_rfd1_wb, exec_ext_adr}), // LSU_RSVRS
    //  ## passing only with writting back
    .padv_wb_i                  (padv_wb), // LSU_RSVRS
    // Hazard could be resolving
    //  ## packed input
    .wb2exe_hazards_data_i      ({wb_rfd2_wb, wb_rfd1_wb, // LSU_RSVRS
                                  wb_rfd1_adr[(DEST_REG_ADDR_WIDTH-1):OPTION_RF_ADDR_WIDTH]}), // LSU_RSVRS
    //  ## forwarding results
    .wb_result1_i               (wb_result1), // LSU_RSVRS
    .wb_result2_i               (wb_result2), // LSU_RSVRS
    // Processing of LSU's WB-miss
    .wb_rfd1_wb_lsu_miss_i      (wb_rfd1_wb_lsu_miss), // LSU_RSVRS
    // command and its additional attributes
    .dcod_op_i                  (dcod_op_lsu_load | dcod_op_lsu_store | dcod_op_msync), // LSU_RSVRS
    .dcod_opc_i                 ({dcod_op_lsu_load,dcod_op_lsu_store,dcod_op_lsu_atomic, // LSU_RSVRS
                                 dcod_lsu_length,dcod_lsu_zext, // LSU_RSVRS
                                  dcod_op_msync, // LSU_RSVRS
                                  dcod_imm16,dcod_sbuf_epcr}), // LSU_RSVRS
    // outputs
    //   command attributes from busy stage
    .busy_opc_o                 (), // LSU_RSVRS
    //   combined D1XX hazards
    .exec_wb2exe_hazard_d1xx_o  (), // LSU_RSVRS
    //   command and its additional attributes
    .exec_op_o                  (), // LSU_RSVRS
    .exec_opc_o                 ({exec_op_lsu_load,exec_op_lsu_store,exec_op_lsu_atomic, // LSU_RSVRS
                                  exec_lsu_length,exec_lsu_zext, // LSU_RSVRS
                                  exec_op_msync, // LSU_RSVRS
                                  exec_lsu_imm16,exec_sbuf_epcr}), // LSU_RSVRS
    //   operands
    .exec_rfa1_o                (exec_lsu_a1), // LSU_RSVRS
    .exec_rfb1_o                (exec_lsu_b1), // LSU_RSVRS
    //  ## for FPU64
    .exec_rfa2_o                (), // LSU_RSVRS
    .exec_rfb2_o                (), // LSU_RSVRS
    //   unit-is-busy flag
    .unit_busy_o                (lsu_busy) // LSU_RSVRS
  );


  // **** LSU instance ****
  mor1kx_lsu_marocchino
  #(
    .OPTION_OPERAND_WIDTH               (OPTION_OPERAND_WIDTH), // LSU
    .OPTION_DCACHE_BLOCK_WIDTH          (OPTION_DCACHE_BLOCK_WIDTH), // LSU
    .OPTION_DCACHE_SET_WIDTH            (OPTION_DCACHE_SET_WIDTH), // LSU
    .OPTION_DCACHE_WAYS                 (OPTION_DCACHE_WAYS), // LSU
    .OPTION_DCACHE_LIMIT_WIDTH          (OPTION_DCACHE_LIMIT_WIDTH), // LSU
    .OPTION_DCACHE_SNOOP                (OPTION_DCACHE_SNOOP), // LSU
    .OPTION_DCACHE_CLEAR_ON_INIT        (OPTION_DCACHE_CLEAR_ON_INIT), // LSU
    .FEATURE_DMMU_HW_TLB_RELOAD         (FEATURE_DMMU_HW_TLB_RELOAD), // LSU
    .OPTION_DMMU_SET_WIDTH              (OPTION_DMMU_SET_WIDTH), // LSU
    .OPTION_DMMU_WAYS                   (OPTION_DMMU_WAYS), // LSU
    .OPTION_DMMU_CLEAR_ON_INIT          (OPTION_DMMU_CLEAR_ON_INIT), // LSU
    .OPTION_STORE_BUFFER_DEPTH_WIDTH    (OPTION_STORE_BUFFER_DEPTH_WIDTH), // LSU
    .OPTION_STORE_BUFFER_CLEAR_ON_INIT  (OPTION_STORE_BUFFER_CLEAR_ON_INIT) // LSU
  )
  u_lsu
  (
    // clocks & resets
    .clk                              (clk), // LSU
    .rst                              (rst), // LSU
    // Pipeline controls
    .pipeline_flush_i                 (pipeline_flush), // LSU
    .padv_wb_i                        (padv_wb), // LSU
    .grant_wb_to_lsu_i                (grant_wb_to_lsu), // LSU
    // configuration
    .dc_enable_i                      (dc_enable), // LSU
    .dmmu_enable_i                    (dmmu_enable), // LSU
    .supervisor_mode_i                (supervisor_mode), // LSU
    // Input from DECODE (not latched)
    .exec_sbuf_epcr_i                 (exec_sbuf_epcr), // LSU (for store buffer EPCR computation)
    .exec_lsu_imm16_i                 (exec_lsu_imm16), // LSU
    .exec_lsu_a1_i                    (exec_lsu_a1), // LSU
    .exec_lsu_b1_i                    (exec_lsu_b1), // LSU
    .exec_op_lsu_load_i               (exec_op_lsu_load), // LSU
    .exec_op_lsu_store_i              (exec_op_lsu_store), // LSU
    .exec_op_lsu_atomic_i             (exec_op_lsu_atomic), // LSU
    .exec_lsu_length_i                (exec_lsu_length), // LSU
    .exec_lsu_zext_i                  (exec_lsu_zext), // LSU
    .exec_op_msync_i                  (exec_op_msync), // LSU
    // inter-module interface
    .spr_bus_addr_i                   (spr_bus_addr_o), // LSU
    .spr_bus_we_i                     (spr_bus_we_o), // LSU
    .spr_bus_stb_i                    (spr_bus_stb_o), // LSU
    .spr_bus_dat_i                    (spr_bus_dat_o), // LSU
    .spr_bus_dat_dc_o                 (spr_bus_dat_dc), // LSU
    .spr_bus_ack_dc_o                 (spr_bus_ack_dc), // LSU
    .spr_bus_dat_dmmu_o               (spr_bus_dat_dmmu), // LSU
    .spr_bus_ack_dmmu_o               (spr_bus_ack_dmmu), // LSU
    // DBUS bridge interface
    .dbus_err_i                       (dbus_err_i), // LSU
    .dbus_ack_i                       (dbus_ack_i), // LSU
    .dbus_dat_i                       (dbus_dat_i[OPTION_OPERAND_WIDTH-1:0]), // LSU
    .dbus_adr_o                       (dbus_adr_o), // LSU
    .dbus_req_o                       (dbus_req_o), // LSU
    .dbus_dat_o                       (dbus_dat_o), // LSU
    .dbus_bsel_o                      (dbus_bsel_o[3:0]), // LSU
    .dbus_we_o                        (dbus_we_o), // LSU
    .dbus_burst_o                     (dbus_burst_o), // LSU
    // Cache sync for multi-core environment
    .snoop_adr_i                      (snoop_adr_i[31:0]), // LSU
    .snoop_en_i                       (snoop_en_i), // LSU
    // Output flags and load result
    .lsu_taking_op_o                  (lsu_taking_op), // LSU
    .lsu_valid_o                      (lsu_valid), // LSU: result ready or exceptions
    .wb_lsu_result_o                  (wb_lsu_result), // LSU
    .wb_lsu_valid_miss_o              (wb_lsu_valid_miss), // LSU
    .wb_rfd1_wb_lsu_miss_o            (wb_rfd1_wb_lsu_miss), // LSU
    .wb_flag_wb_lsu_miss_o            (wb_flag_wb_lsu_miss), // LSU
    // Exceprions & errors
    .sbuf_eear_o                      (sbuf_eear), // LSU
    .sbuf_epcr_o                      (sbuf_epcr), // LSU
    .sbuf_err_o                       (sbuf_err), // LSU
    //  # particular LSU exception flags
    .wb_except_dbus_err_o             (wb_except_dbus_err), // LSU
    .wb_except_dpagefault_o           (wb_except_dpagefault), // LSU
    .wb_except_dtlb_miss_o            (wb_except_dtlb_miss), // LSU
    .wb_except_dbus_align_o           (wb_except_dbus_align), // LSU
    .wb_lsu_except_addr_o             (wb_lsu_except_addr), // LSU
    //  # combined LSU exceptions flag
    .wb_an_except_lsu_o               (wb_an_except_lsu), // LSU

    .wb_atomic_flag_set_o             (wb_atomic_flag_set), // LSU
    .wb_atomic_flag_clear_o           (wb_atomic_flag_clear) // LSU
  );


  //-----------//
  // WB:result //
  //-----------//

  assign wb_result1 =  wb_alu_1clk_result   |
                       wb_div_result        | wb_mul_result |
                       wb_fpxx_arith_res_hi |
                       wb_lsu_result        | wb_mfspr_dat;

  assign wb_result2 = wb_fpxx_arith_res_lo;


  //------------------------------------//
  // WB: External Interrupts Collection //
  //------------------------------------//
  wire exec_tt_interrupt  = tt_rdy       & tt_interrupt_enable  & exec_interrupts_en; // from "Tick Timer"
  wire exec_pic_interrupt = (|spr_picsr) & pic_interrupt_enable & exec_interrupts_en; // from "Programmble Interrupt Controller"
  // --- wb-latches ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      wb_tt_interrupt_r   <= 1'b0;
      wb_pic_interrupt_r  <= 1'b0;
      wb_an_interrupt_r   <= 1'b0;
    end
    else if (pipeline_flush) begin  // WB: External Interrupts Collection
      wb_tt_interrupt_r   <= 1'b0;
      wb_pic_interrupt_r  <= 1'b0;
      wb_an_interrupt_r   <= 1'b0;
    end
    else if (padv_wb) begin  // WB: External Interrupts Collection
      wb_tt_interrupt_r   <= exec_tt_interrupt;
      wb_pic_interrupt_r  <= exec_pic_interrupt;
      wb_an_interrupt_r   <= (exec_tt_interrupt | exec_pic_interrupt);
    end
  end // @clock


  //-------//
  // TIMER //
  //-------//
  //  # connection wires
  wire [31:0] spr_bus_dat_tt;
  wire        spr_bus_ack_tt;
  //  # timer instance
  mor1kx_ticktimer_oneself u_ticktimer
  (
    // clock and reset
    .clk                (clk), // TIMER
    .rst                (rst), // TIMER
    // ready flag
    .tt_rdy_o           (tt_rdy), // TIMER
    // SPR interface
    .spr_bus_addr_i     (spr_bus_addr_o), // TIMER
    .spr_bus_we_i       (spr_bus_we_o), // TIMER
    .spr_bus_stb_i      (spr_bus_stb_o), // TIMER
    .spr_bus_dat_i      (spr_bus_dat_o), // TIMER
    .spr_bus_dat_tt_o   (spr_bus_dat_tt), // TIMER
    .spr_bus_ack_tt_o   (spr_bus_ack_tt) // TIMER
  );


  //-----//
  // PIC //
  //-----//
  //  # connection wires
  wire [31:0] spr_bus_dat_pic;
  wire        spr_bus_ack_pic;
  //  # timer instance
  mor1kx_pic_oneself
  #(
    .OPTION_PIC_TRIGGER   (OPTION_PIC_TRIGGER), // PIC
    .OPTION_PIC_NMI_WIDTH (OPTION_PIC_NMI_WIDTH) // PIC
  )
  u_pic
  (
    // clock and reset
    .clk                (clk), // PIC
    .rst                (rst), // PIC
    // input interrupt lines
    .irq_i              (irq_i), // PIC
    // output interrupt lines
    .spr_picsr_o        (spr_picsr), // PIC
    // SPR BUS
    //  # inputs
    .spr_bus_addr_i     (spr_bus_addr_o), // PIC
    .spr_bus_we_i       (spr_bus_we_o), // PIC
    .spr_bus_stb_i      (spr_bus_stb_o), // PIC
    .spr_bus_dat_i      (spr_bus_dat_o), // PIC
    //  # outputs
    .spr_bus_dat_pic_o  (spr_bus_dat_pic), // PIC
    .spr_bus_ack_pic_o  (spr_bus_ack_pic) // PIC
  );


  //------//
  // CTRL //
  //------//
  mor1kx_ctrl_marocchino
  #(
    .OPTION_OPERAND_WIDTH       (OPTION_OPERAND_WIDTH), // CTRL
    .OPTION_RESET_PC            (OPTION_RESET_PC), // CTRL
    .OPTION_PIC_TRIGGER         (OPTION_PIC_TRIGGER), // CTRL
    .OPTION_DCACHE_BLOCK_WIDTH  (OPTION_DCACHE_BLOCK_WIDTH), // CTRL
    .OPTION_DCACHE_SET_WIDTH    (OPTION_DCACHE_SET_WIDTH), // CTRL
    .OPTION_DCACHE_WAYS         (OPTION_DCACHE_WAYS), // CTRL
    .OPTION_DMMU_SET_WIDTH      (OPTION_DMMU_SET_WIDTH), // CTRL
    .OPTION_DMMU_WAYS           (OPTION_DMMU_WAYS), // CTRL
    .OPTION_ICACHE_BLOCK_WIDTH  (OPTION_ICACHE_BLOCK_WIDTH), // CTRL
    .OPTION_ICACHE_SET_WIDTH    (OPTION_ICACHE_SET_WIDTH), // CTRL
    .OPTION_ICACHE_WAYS         (OPTION_ICACHE_WAYS), // CTRL
    .OPTION_IMMU_SET_WIDTH      (OPTION_IMMU_SET_WIDTH), // CTRL
    .OPTION_IMMU_WAYS           (OPTION_IMMU_WAYS), // CTRL
    .FEATURE_DEBUGUNIT          (FEATURE_DEBUGUNIT), // CTRL
    .FEATURE_PERFCOUNTERS       (FEATURE_PERFCOUNTERS), // CTRL
    .FEATURE_MAC                ("NONE"), // CTRL
    .FEATURE_MULTICORE          (FEATURE_MULTICORE) // CTRL
  )
  u_ctrl
  (
    // clocks & resets
    .clk                              (clk), // CTRL
    .rst                              (rst), // CTRL

    // Inputs / Outputs for pipeline control signals
    .dcod_insn_valid_i                (dcod_insn_valid), // CTRL
    .fetch_an_except_i                (fetch_an_except), // CTRL
    .exec_an_except_i                 (exec_an_except), // CTRL
    .dcod_valid_i                     (dcod_valid), // CTRL
    .exec_valid_i                     (exec_valid), // CTRL
    .pipeline_flush_o                 (pipeline_flush), // CTRL
    .padv_fetch_o                     (padv_fetch), // CTRL
    .padv_decode_o                    (padv_decode), // CTRL
    .padv_wb_o                        (padv_wb), // CTRL

    // MF(T)SPR coomand processing
    //  ## iput data & command from DECODE
    .dcod_rfa1_i                      (dcod_rfa1), // CTRL: part of addr for MT(F)SPR
    .dcod_imm16_i                     (dcod_imm16), // CTRL: part of addr for MT(F)SPR
    .dcod_rfb1_i                      (dcod_rfb1), // CTRL: data for MTSPR
    .dcod_op_mfspr_i                  (dcod_op_mfspr), // CTRL
    .dcod_op_mtspr_i                  (dcod_op_mtspr), // CTRL
    //  ## result to WB_MUX
    .wb_mfspr_dat_o                   (wb_mfspr_dat), // CTRL: for WB_MUX

    // Track branch address for exception processing support
    .dcod_do_branch_i                 (dcod_do_branch), // CTRL
    .dcod_do_branch_target_i          (dcod_do_branch_target), // CTRL
    //.dcod_jump_or_branch_i            (dcod_jump_or_branch), // CTRL
    // Support IBUS error handling in CTRL
    .exec_jump_or_branch_i            (exec_jump_or_branch), // CTRL
    .pc_exec_i                        (pc_exec), // CTRL

    // Debug System accesses CPU SPRs through DU
    .du_addr_i                        (du_addr_i), // CTRL
    .du_stb_i                         (du_stb_i), // CTRL
    .du_dat_i                         (du_dat_i), // CTRL
    .du_we_i                          (du_we_i), // CTRL
    .du_dat_o                         (du_dat_o), // CTRL
    .du_ack_o                         (du_ack_o), // CTRL
    // Stall control from debug interface
    .du_stall_i                       (du_stall_i), // CTRL
    .du_stall_o                       (du_stall_o), // CTRL
    // Enable l.trap exception
    .du_trap_enable_o                 (du_trap_enable), // CTRL

    // SPR accesses to external units (cache, mmu, etc.)
    .spr_bus_addr_o                   (spr_bus_addr_o), // CTRL
    .spr_bus_we_o                     (spr_bus_we_o), // CTRL
    .spr_bus_stb_o                    (spr_bus_stb_o), // CTRL
    .spr_bus_dat_o                    (spr_bus_dat_o), // CTRL
    .spr_bus_dat_dc_i                 (spr_bus_dat_dc), // CTRL
    .spr_bus_ack_dc_i                 (spr_bus_ack_dc), // CTRL
    .spr_bus_dat_ic_i                 (spr_bus_dat_ic), // CTRL
    .spr_bus_ack_ic_i                 (spr_bus_ack_ic), // CTRL
    .spr_bus_dat_dmmu_i               (spr_bus_dat_dmmu), // CTRL
    .spr_bus_ack_dmmu_i               (spr_bus_ack_dmmu), // CTRL
    .spr_bus_dat_immu_i               (spr_bus_dat_immu), // CTRL
    .spr_bus_ack_immu_i               (spr_bus_ack_immu), // CTRL
    .spr_bus_dat_mac_i                ({OPTION_OPERAND_WIDTH{1'b0}}), // CTRL
    .spr_bus_ack_mac_i                (1'b0), // CTRL
    .spr_bus_dat_pmu_i                ({OPTION_OPERAND_WIDTH{1'b0}}), // CTRL
    .spr_bus_ack_pmu_i                (1'b0), // CTRL
    .spr_bus_dat_pcu_i                ({OPTION_OPERAND_WIDTH{1'b0}}), // CTRL
    .spr_bus_ack_pcu_i                (1'b0), // CTRL
    .spr_bus_dat_fpu_i                ({OPTION_OPERAND_WIDTH{1'b0}}), // CTRL
    .spr_bus_ack_fpu_i                (1'b0), // CTRL
    .spr_bus_dat_tt_i                 (spr_bus_dat_tt), // CTRL
    .spr_bus_ack_tt_i                 (spr_bus_ack_tt), // CTRL
    .spr_bus_dat_pic_i                (spr_bus_dat_pic), // CTRL
    .spr_bus_ack_pic_i                (spr_bus_ack_pic), // CTRL
    .spr_bus_dat_gpr_i                (spr_bus_dat_gpr), // CTRL
    .spr_bus_ack_gpr_i                (spr_bus_ack_gpr), // CTRL

    // WB: External Interrupt Collection
    .tt_interrupt_enable_o            (tt_interrupt_enable), // CTRL
    .pic_interrupt_enable_o           (pic_interrupt_enable), // CTRL
    .wb_tt_interrupt_i                (wb_tt_interrupt_r), // CTRL
    .wb_pic_interrupt_i               (wb_pic_interrupt_r), // CTRL
    .wb_an_interrupt_i                (wb_an_interrupt_r), // CTRL

    // WB: programm counter
    .pc_wb_i                          (pc_wb), // CTRL

    // WB: flag
    .wb_int_flag_set_i                (wb_int_flag_set), // CTRL
    .wb_int_flag_clear_i              (wb_int_flag_clear), // CTRL
    .wb_fp32_flag_set_i               (wb_fp32_flag_set), // CTRL
    .wb_fp32_flag_clear_i             (wb_fp32_flag_clear), // CTRL
    .wb_fp64_flag_set_i               (wb_fp64_flag_set), // CTRL
    .wb_fp64_flag_clear_i             (wb_fp64_flag_clear), // CTRL
    .wb_atomic_flag_set_i             (wb_atomic_flag_set), // CTRL
    .wb_atomic_flag_clear_i           (wb_atomic_flag_clear), // CTRL
    .wb_flag_wb_i                     (wb_flag_wb), // CTRL

    // WB: carry
    .wb_div_carry_set_i               (wb_div_carry_set), // CTRL
    .wb_div_carry_clear_i             (wb_div_carry_clear), // CTRL
    .wb_1clk_carry_set_i              (wb_1clk_carry_set), // CTRL
    .wb_1clk_carry_clear_i            (wb_1clk_carry_clear), // CTRL
    .wb_carry_wb_i                    (wb_carry_wb), // CTRL

    // WB: overflow
    .wb_div_overflow_set_i            (wb_div_overflow_set), // CTRL
    .wb_div_overflow_clear_i          (wb_div_overflow_clear), // CTRL
    .wb_1clk_overflow_set_i           (wb_1clk_overflow_set), // CTRL
    .wb_1clk_overflow_clear_i         (wb_1clk_overflow_clear), // CTRL

    //  # FPX32 related flags
    //    ## comparison part
    .wb_fp32_cmp_inv_i                (wb_fp32_cmp_inv), // CTRL
    .wb_fp32_cmp_inf_i                (wb_fp32_cmp_inf), // CTRL
    .wb_fp32_cmp_wb_fpcsr_i           (wb_fp32_cmp_wb_fpcsr), // CTRL
    .wb_except_fp32_cmp_i             (wb_except_fp32_cmp), // CTRL

    //  # FPX3264 arithmetic part
    .wb_fpxx_arith_fpcsr_i            (wb_fpxx_arith_fpcsr), // CTRL
    .wb_fpxx_arith_wb_fpcsr_i         (wb_fpxx_arith_wb_fpcsr), // CTRL
    .wb_except_fpxx_arith_i           (wb_except_fpxx_arith), // CTRL
    //  # FPX64 comparison part
    .wb_fp64_cmp_inv_i                (wb_fp64_cmp_inv), // CTRL
    .wb_fp64_cmp_inf_i                (wb_fp64_cmp_inf), // CTRL
    .wb_fp64_cmp_wb_fpcsr_i           (wb_fp64_cmp_wb_fpcsr), // CTRL
    .wb_except_fp64_cmp_i             (wb_except_fp64_cmp), // CTRL

    //  # Excepion processing auxiliaries
    .sbuf_eear_i                      (sbuf_eear), // CTRL
    .sbuf_epcr_i                      (sbuf_epcr), // CTRL
    .sbuf_err_i                       (sbuf_err), // CTRL
    .wb_delay_slot_i                  (wb_delay_slot), // CTRL

    //  # particular IFETCH exception flags
    .wb_except_ibus_err_i             (wb_except_ibus_err), // CTRL
    .wb_except_itlb_miss_i            (wb_except_itlb_miss), // CTRL
    .wb_except_ipagefault_i           (wb_except_ipagefault), // CTRL
    .wb_except_ibus_align_i           (wb_except_ibus_align), // CTRL
    .wb_lsu_except_addr_i             (wb_lsu_except_addr), // CTRL
    //  # particular DECODE exception flags
    .wb_except_illegal_i              (wb_except_illegal), // CTRL
    .wb_except_syscall_i              (wb_except_syscall), // CTRL
    .wb_except_trap_i                 (wb_except_trap), // CTRL
    //  # combined DECODE/IFETCH exceptions flag
    .wb_fd_an_except_i                (wb_fd_an_except), // CTRL
    //  # LSU valid is miss (block padv-wb)
    .wb_lsu_valid_miss_i              (wb_lsu_valid_miss), // CTRL: block padv-wb

    //  # particular LSU exception flags
    .wb_except_dbus_err_i             (wb_except_dbus_err), // CTRL
    .wb_except_dtlb_miss_i            (wb_except_dtlb_miss), // CTRL
    .wb_except_dpagefault_i           (wb_except_dpagefault), // CTRL
    .wb_except_dbus_align_i           (wb_except_dbus_align), // CTRL
    //  # combined LSU exceptions flag
    .wb_an_except_lsu_i               (wb_an_except_lsu), // CTRL

    //  # overflow exception processing
    .except_overflow_enable_o         (except_overflow_enable), // CTRL
    .wb_except_overflow_div_i         (wb_except_overflow_div), // CTRL
    .wb_except_overflow_1clk_i        (wb_except_overflow_1clk), // CTRL

    //  # Branch to exception/rfe processing address
    .ctrl_branch_exception_o          (ctrl_branch_exception), // CTRL
    .ctrl_branch_except_pc_o          (ctrl_branch_except_pc), // CTRL
    .fetch_exception_taken_i          (fetch_ecxeption_taken), // CTRL
    //  # l.rfe
    .wb_op_rfe_i                      (wb_op_rfe), // CTRL

    // Multicore related
    .multicore_coreid_i               (multicore_coreid_i), // CTRL
    .multicore_numcores_i             (multicore_numcores_i), // CTRL

    // Flag & Carry
    .ctrl_flag_o                      (ctrl_flag), // CTRL
    .ctrl_carry_o                     (ctrl_carry), // CTRL

    // Enable modules
    .ic_enable_o                      (ic_enable), // CTRL
    .immu_enable_o                    (immu_enable), // CTRL
    .dc_enable_o                      (dc_enable), // CTRL
    .dmmu_enable_o                    (dmmu_enable), // CTRL
    .supervisor_mode_o                (supervisor_mode), // CTRL

    // FPU rounding mode
    .except_fpu_enable_o              (except_fpu_enable), // CTRL
    .ctrl_fpu_mask_flags_o            (ctrl_fpu_mask_flags), // CTRL
    .ctrl_fpu_round_mode_o            (ctrl_fpu_round_mode) // CTRL
  );

/*
   reg [`OR1K_INSN_WIDTH-1:0] traceport_stage_dcod_insn;
   reg [`OR1K_INSN_WIDTH-1:0] traceport_stage_exec_insn;

   reg            traceport_waitexec;

   always @(posedge clk) begin
      if (FEATURE_TRACEPORT_EXEC != "NONE") begin
   if (rst) begin
      traceport_waitexec <= 0;
   end else begin
      if (padv_decode) begin
         traceport_stage_dcod_insn <= dcod_insn;
      end

      if (padv_execute) begin
         traceport_stage_exec_insn <= traceport_stage_dcod_insn;
      end

      if (ctrl_new_input) begin
         traceport_exec_insn_o <= traceport_stage_exec_insn;
      end

      traceport_exec_pc_o <= pc_ctrl;
      if (!traceport_waitexec) begin
         if (ctrl_new_input & !ctrl_bubble) begin
      if (exec_valid) begin
         traceport_exec_valid_o <= 1'b1;
      end else begin
         traceport_exec_valid_o <= 1'b0;
         traceport_waitexec <= 1'b1;
      end
         end else begin
      traceport_exec_valid_o <= 1'b0;
         end
      end else begin
         if (exec_valid) begin
      traceport_exec_valid_o <= 1'b1;
      traceport_waitexec <= 1'b0;
         end else begin
      traceport_exec_valid_o <= 1'b0;
         end
      end // else: !if(!traceport_waitexec)
   end // else: !if(rst)
      end else begin // if (FEATURE_TRACEPORT_EXEC != "NONE")
   traceport_stage_dcod_insn <= {`OR1K_INSN_WIDTH{1'b0}};
   traceport_stage_exec_insn <= {`OR1K_INSN_WIDTH{1'b0}};
   traceport_exec_insn_o <= {`OR1K_INSN_WIDTH{1'b0}};
   traceport_exec_pc_o <= 32'h0;
   traceport_exec_valid_o <= 1'b0;
      end
   end

   generate
      if (FEATURE_TRACEPORT_EXEC != "NONE") begin
   assign traceport_exec_wbreg_o = wb_rfd1_adr;
   assign traceport_exec_wben_o = wb_rfd1_wb;
   assign traceport_exec_wbdata_o = wb_result1;
      end else begin
   assign traceport_exec_wbreg_o = {OPTION_RF_ADDR_WIDTH{1'b0}};
   assign traceport_exec_wben_o = 1'b0;
   assign traceport_exec_wbdata_o = {OPTION_OPERAND_WIDTH{1'b0}};
      end
   endgenerate
*/
endmodule // mor1kx_cpu_marocchino
