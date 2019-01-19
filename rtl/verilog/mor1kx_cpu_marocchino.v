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
//   Copyright (C) 2015 - 2018 Andrey Bacherov                        //
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
  // temporary:
  parameter OPTION_ORFPX64A32_ABI       = "GCC5", // "GCC9" / "GCC5"
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
  // write buffer
  parameter OPTION_STORE_BUFFER_DEPTH_WIDTH   = 4, // 16 taps
  parameter OPTION_STORE_BUFFER_CLEAR_ON_INIT = 0,
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
  // interrupt controller
  parameter OPTION_PIC_TRIGGER          = "LEVEL",
  parameter OPTION_PIC_NMI_WIDTH        = 0,
  // debug unit, performance counters, trace
  parameter FEATURE_DEBUGUNIT           = "NONE",
  parameter FEATURE_PERFCOUNTERS        = "NONE",
  // m-core
  parameter FEATURE_MULTICORE           = "NONE",
  parameter OPTION_RF_NUM_SHADOW_GPR    = 0,      // for multicore mostly
  // Redister File
  parameter OPTION_RF_CLEAR_ON_INIT     = 0,
  parameter OPTION_RF_ADDR_WIDTH        = 5,
  // starting PC
  parameter OPTION_RESET_PC             = {{(OPTION_OPERAND_WIDTH-13){1'b0}},
                                           `OR1K_RESET_VECTOR,8'd0},
  // special instructions
  parameter FEATURE_PSYNC               = "NONE",
  parameter FEATURE_CSYNC               = "NONE"
)
(
  // Wishbone clock and reset
  input                             wb_clk,
  input                             wb_rst,

  // CPU clock and reset
  input                             cpu_clk,
  input                             cpu_rst,
  // For lwa/swa
  output                            pipeline_flush_o,

  // Instruction bus
  input                             ibus_err_i,
  input                             ibus_ack_i,
  input      [`OR1K_INSN_WIDTH-1:0] ibus_dat_i,
  input                             ibus_burst_last_i,
  output [OPTION_OPERAND_WIDTH-1:0] ibus_adr_o,
  output                            ibus_req_o,
  output                            ibus_burst_o,

  // Data bus
  input                             dbus_err_i,
  input                             dbus_ack_i,
  input  [OPTION_OPERAND_WIDTH-1:0] dbus_dat_i,
  input                             dbus_burst_last_i,
  output [OPTION_OPERAND_WIDTH-1:0] dbus_adr_o,
  output [OPTION_OPERAND_WIDTH-1:0] dbus_dat_o,
  output                            dbus_req_o,
  output                      [3:0] dbus_bsel_o,
  output                            dbus_lwa_cmd_o, // atomic load
  output                            dbus_stna_cmd_o, // none-atomic store
  output                            dbus_swa_cmd_o, // atomic store
  output                            dbus_burst_o,
  // Other connections for lwa/swa support
  input                             dbus_atomic_flg_i,

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

  // SPR accesses to external units (cache, mmu, etc.)
  output [15:0]                     spr_bus_addr_o,
  output                            spr_bus_we_o,
  output                            spr_bus_stb_o,
  output [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o,

  // multi-core
  input  [OPTION_OPERAND_WIDTH-1:0] multicore_coreid_i,
  input  [OPTION_OPERAND_WIDTH-1:0] multicore_numcores_i,
  input                      [31:0] snoop_adr_i,
  input                             snoop_en_i
);

  localparam DEST_EXTADR_WIDTH  = 3; // log2(Order Control Buffer depth)

  // branch predictor parameters
  localparam GSHARE_BITS_NUM      = 12;

  localparam NUM_GPRS = (1 << OPTION_RF_ADDR_WIDTH);


  // Instruction PC
  wire [OPTION_OPERAND_WIDTH-1:0] pc_fetch;
  wire [OPTION_OPERAND_WIDTH-1:0] pc_decode;
  wire [OPTION_OPERAND_WIDTH-1:0] pc_wrbk;
  // Extra PC for various needs in CTRL
  wire [OPTION_OPERAND_WIDTH-1:0] pc_nxt_wrbk;
  wire [OPTION_OPERAND_WIDTH-1:0] pc_nxt2_wrbk;


  // IFETCH outputs for RF reading and DECODE
  //  # instruction word valid flag
  wire                            fetch_valid;
  //  # instruction is in delay slot
  wire                            fetch_delay_slot;
  //  # instruction word itsef
  wire     [`OR1K_INSN_WIDTH-1:0] fetch_insn;
  //  # operand addresses
  wire [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfa1_adr;
  wire [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfb1_adr;
  wire [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfa2_adr;
  wire [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfb2_adr;
  //  # destiny addresses
  wire [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfd1_adr;
  wire [OPTION_RF_ADDR_WIDTH-1:0] fetch_rfd2_adr;


  wire                            dcod_empty;


  wire                            wrbk_atomic_flag_set;
  wire                            wrbk_atomic_flag_clear;

  wire                            wrbk_1clk_flag_set;
  wire                            wrbk_1clk_flag_clear;

  wire                            ctrl_flag;
  wire                            ctrl_flag_sr;
  wire                            ctrl_carry;

  wire                            dcod_flag_we; // instruction writes comparison flag

  wire                            dcod_op_mtspr;
  wire                            dcod_op_mXspr; // (l.mfspr | l.mtspr)


  // Write-back outputs per execution unit
  // !!! Copies are usefull mostly for FPGA implementation to simplify routing
  // !!! Don't acivate "Remove duplicate registers" option in
  // !!! MAROCCHINO_TODO: <determine optimal settings>
  //  # from 1-clock execution units
  wire [OPTION_OPERAND_WIDTH-1:0] wrbk_1clk_result;
  //  # from integer division execution unit
  wire [OPTION_OPERAND_WIDTH-1:0] wrbk_div_result;
  //  # from integer multiplier execution unit
  wire [OPTION_OPERAND_WIDTH-1:0] wrbk_mul_result;
  //  # from FP32 execution unit
  wire [OPTION_OPERAND_WIDTH-1:0] wrbk_fpxx_arith_res_hi;
  //  # from FP64 execution unit
  wire [OPTION_OPERAND_WIDTH-1:0] wrbk_fpxx_arith_res_lo;
  //  # from LSU execution unit
  wire [OPTION_OPERAND_WIDTH-1:0] wrbk_lsu_result;
  //  # from CTRL execution unit
  wire [OPTION_OPERAND_WIDTH-1:0] wrbk_mfspr_result;
  // Combined write-back outputs
  //  # regular result
  reg  [OPTION_OPERAND_WIDTH-1:0] wrbk_result1;     // Write-Back result combiner
  //  # extention for FPU3264
  wire [OPTION_OPERAND_WIDTH-1:0] wrbk_result2;     // Write-Back result combiner for FPU64


  wire                            dcod_free;
  wire                            exec_valid;
  wire                            lsu_valid;   // result ready or exceptions


  wire [OPTION_OPERAND_WIDTH-1:0] dcod_rfa1;
  wire [OPTION_OPERAND_WIDTH-1:0] dcod_rfb1;
  wire [OPTION_OPERAND_WIDTH-1:0] dcod_immediate;
  wire                            dcod_immediate_sel;
  // Special case for l.jr/l.jalr
  wire [OPTION_OPERAND_WIDTH-1:0] dcod_rfb1_jr;
  // for FPU64:
  wire [OPTION_OPERAND_WIDTH-1:0] dcod_rfa2;
  wire [OPTION_OPERAND_WIDTH-1:0] dcod_rfb2;


  wire                            dcod_rfd1_we;
  wire [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfd1_adr;
  // for FPU64:
  wire                            dcod_rfd2_we;
  wire [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfd2_adr;


  // OMAN-to-DECODE hazards
  //  # relative operand A1
  wire                            dcod_rfa1_req;
  wire [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa1_adr;
  wire                            omn2dec_hazard_d1a1;
  wire                            omn2dec_hazard_d2a1;
  wire    [DEST_EXTADR_WIDTH-1:0] omn2dec_extadr_dxa1;
  //  # relative operand B1
  wire                            dcod_rfb1_req;
  wire [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb1_adr;
  wire                            omn2dec_hazard_d1b1;
  wire                            omn2dec_hazard_d2b1;
  wire    [DEST_EXTADR_WIDTH-1:0] omn2dec_extadr_dxb1;
  //  # relative operand A2
  wire                            dcod_rfa2_req;
  wire [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfa2_adr;
  wire                            omn2dec_hazard_d1a2;
  wire                            omn2dec_hazard_d2a2;
  wire    [DEST_EXTADR_WIDTH-1:0] omn2dec_extadr_dxa2;
  //  # relative operand B2
  wire                            dcod_rfb2_req;
  wire [OPTION_RF_ADDR_WIDTH-1:0] dcod_rfb2_adr;
  wire                            omn2dec_hazard_d1b2;
  wire                            omn2dec_hazard_d2b2;
  wire    [DEST_EXTADR_WIDTH-1:0] omn2dec_extadr_dxb2;


  // support in-1clk-unit forwarding
  wire    [DEST_EXTADR_WIDTH-1:0] dcod_extadr;
  // for hazards resolution in RSRVS
  wire    [DEST_EXTADR_WIDTH-1:0] wrbk_extadr;


  // Write-Back-controls for RF
  wire             [NUM_GPRS-1:0] wrbk_rfd1_we1h;
  wire                            wrbk_rfd1_we;
  wire [OPTION_RF_ADDR_WIDTH-1:0] wrbk_rfd1_adr;
  // for FPU64:
  wire             [NUM_GPRS-1:0] wrbk_rfd2_we1h;
  wire                            wrbk_rfd2_we;
  wire [OPTION_RF_ADDR_WIDTH-1:0] wrbk_rfd2_adr;


  // Logic to support Jump / Branch taking
  //  # from FETCH
  //    ## jump/branch variants
  wire                            fetch_op_jimm;
  wire                            fetch_op_jr;
  wire                            fetch_op_bf;
  wire                            fetch_op_bnf;
  //    ## combined jump/branch flag
  wire                            fetch_op_jb;
  //    ## pc-relative target
  wire [OPTION_OPERAND_WIDTH-1:0] fetch_to_imm_target;
  //  ## l.jr / l.jalr  gathering target
  wire                            jr_gathering_target;
  //  ## support IBUS error handling in CTRL
  wire                            wrbk_jump_or_branch;
  //  ## do branch (pedicted or unconditional)
  wire                            do_branch;
  wire [OPTION_OPERAND_WIDTH-1:0] do_branch_target;
  //  ## branch prediction support
  wire [OPTION_OPERAND_WIDTH-1:0] after_ds_target;
  wire                            predict_miss;
  wire                      [1:0] bc_cnt_value;  // current value of saturation counter
  wire      [GSHARE_BITS_NUM-1:0] bc_cnt_radr;   // saturation counter ID
  wire                            bc_cnt_we;     // update saturation counter
  wire                      [1:0] bc_cnt_wdat;   // new saturation counter value
  wire      [GSHARE_BITS_NUM-1:0] bc_cnt_wadr;   // saturation counter id
  wire                            bc_hist_taken; // conditional branch really taken
  //  ## support NPC handling in CTRL
  wire                            wrbk_jump;
  wire                            wrbk_op_bf;
  wire [OPTION_OPERAND_WIDTH-1:0] wrbk_jb_target;


  // Delay slot
  wire                            dcod_delay_slot;
  wire                            wrbk_delay_slot;


  wire      [`OR1K_IMM_WIDTH-1:0] dcod_imm16;
  wire                            dcod_op_lsu_load;
  wire                            dcod_op_lsu_store;
  wire                            dcod_op_lsu_atomic;
  wire                      [1:0] dcod_lsu_length;
  wire                            dcod_lsu_zext;
  wire                            dcod_op_msync;
  wire                            dcod_op_lsu_any;
  wire                            lsu_free;
  wire                            grant_wrbk_to_lsu;


  // Instructions which push EXECUTION without extra conditions
  wire                            dcod_op_push_exec;
  // Instructions which push WRITE-BACK without extra conditions
  wire                            dcod_op_push_wrbk;


  // Reservation station for 1-clock execution units
  wire                            dcod_op_1clk;
  wire                            exec_op_1clk;
  wire                            op_1clk_free;

  wire                            dcod_flag_carry_req;

  wire                            dcod_op_add;
  wire                            dcod_adder_do_sub;
  wire                            dcod_adder_do_carry;

  wire                            dcod_op_jal;

  wire                            dcod_op_shift;
  wire                      [3:0] dcod_opc_shift; // {SLL, SRL, SRA, ROR}

  wire                            dcod_op_ffl1;
  wire                            dcod_opc_ffl1;

  wire                            dcod_op_movhi;
  wire                            dcod_op_cmov;

  wire                            dcod_op_extsz;
  wire                      [3:0] dcod_opc_extsz;

  wire                            dcod_op_logic;
  wire                      [3:0] dcod_lut_logic;

  wire                            dcod_op_setflag;
  wire [`OR1K_COMP_OPC_WIDTH-1:0] dcod_opc_setflag;

  wire                            grant_wrbk_to_1clk;
  wire                            taking_1clk_op;
  wire                            op_1clk_valid;


  // Divider
  wire                            dcod_op_div;
  wire                            dcod_op_div_signed;
  wire                            dcod_op_div_unsigned;
  wire                            div_valid;
  wire                            grant_wrbk_to_div;
  // Pipelined multiplier
  wire                            dcod_op_mul;
  wire                            mul_valid;
  wire                            grant_wrbk_to_mul;
  // Reservation station for integer MUL/DIV
  wire                            dcod_op_muldiv;
  wire                            muldiv_free;


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
  wire                              grant_wrbk_to_fpxx_arith;
  wire                              exec_except_fpxx_arith;
  wire  [`OR1K_FPCSR_ALLF_SIZE-1:0] wrbk_fpxx_arith_fpcsr;    // only flags
  wire                              wrbk_fpxx_arith_fpcsr_we; // update FPCSR
  wire                              wrbk_except_fpxx_arith;   // generate FPx exception by FPx flags
  // FPU3264 comparison part
  wire                              dcod_op_fpxx_cmp;
  wire                        [2:0] dcod_opc_fpxx_cmp;
  wire                              exec_op_fpxx_cmp;
  wire                        [2:0] exec_opc_fpxx_cmp;
  wire                              fpxx_cmp_valid;
  wire                              grant_wrbk_to_fpxx_cmp;
  wire                              exec_except_fpxx_cmp;
  wire                              wrbk_fpxx_flag_set;
  wire                              wrbk_fpxx_flag_clear;
  wire                              wrbk_fpxx_cmp_inv;
  wire                              wrbk_fpxx_cmp_inf;
  wire                              wrbk_fpxx_cmp_fpcsr_we;
  wire                              wrbk_except_fpxx_cmp;
  // FPU3264 reservationstation controls
  wire                              dcod_op_fpxx_any;
  wire                              fpxx_free;
  wire                              fpxx_taking_op;


  wire [OPTION_OPERAND_WIDTH-1:0] sbuf_eear;
  wire [OPTION_OPERAND_WIDTH-1:0] sbuf_epcr;
  wire                            sbuf_err;


  // CTRL -> Unit on Wishbone clock (TT & PIC)
  wire                            spr_bus_toggle;

  // SPR access buses (Unit -> CTRL part)
  //   GPR[0]
  wire                            spr_bus_ack_gpr0;
  wire [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_gpr0;
  //   GPR [S]hadow
  wire                            spr_bus_ack_gprS;
  wire [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_gprS;
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


  // [O]rder [C]ontrol [B]uffer statuses
  wire ocb_full, ocb_empty;

  // pipeline controls from CTRL to units
  wire padv_fetch;
  wire padv_1clk_rsrvs;
  wire padv_muldiv_rsrvs;
  wire padv_fpxx_rsrvs;
  wire padv_lsu_rsrvs;
  wire padv_dcod;
  wire padv_exec;
  wire padv_wrbk;
  wire pipeline_flush;

  // For lwa/swa
  assign pipeline_flush_o = pipeline_flush;

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
  wire fetch_an_except;
  //  # pre-Write-Back IFETCH exceptions (OMAN output)
  wire exec_except_ibus_err;
  wire exec_except_ipagefault;
  wire exec_except_itlb_miss;
  wire exec_except_ibus_align;
  //  # Write-Back-latches for IFETCH exceptions (OMAN->CTRL)
  reg  wrbk_except_ibus_err_r;
  reg  wrbk_except_ipagefault_r;
  reg  wrbk_except_itlb_miss_r;
  reg  wrbk_except_ibus_align_r;

  // Exceptions: reported from DECODE to OMAN
  wire dcod_except_illegal;
  wire dcod_except_syscall;
  wire dcod_except_trap;
  // Enable l.trap exception
  wire du_trap_enable;
  // Exceptions: pre-Write-Back DECODE exceptions (OMAN output)
  wire exec_except_illegal;
  wire exec_except_syscall;
  wire exec_except_trap;
  // Exceptions: latched by Write-Back latches for processing in CONTROL-unit
  reg  wrbk_except_illegal_r;
  reg  wrbk_except_syscall_r;
  reg  wrbk_except_trap_r;

  // combined IFETCH/DECODE an exception flag
  wire dcod_an_except_fd;
  wire exec_an_except_fd;

  //  # overflow exception
  wire except_overflow_enable;
  //    ## from division
  wire exec_except_overflow_div;
  wire wrbk_except_overflow_div;
  //    ## from 1-CLOCK
  wire exec_except_overflow_1clk;
  wire wrbk_except_overflow_1clk;

  // Exceptions: reported by LSU
  //  # particular LSU exception flags
  wire                            wrbk_except_dbus_err;
  wire                            wrbk_except_dpagefault;
  wire                            wrbk_except_dtlb_miss;
  wire                            wrbk_except_dbus_align;
  wire [OPTION_OPERAND_WIDTH-1:0] wrbk_lsu_except_addr;
  //  # combined LSU exceptions flag
  wire                            exec_an_except_lsu;


  // External Interrupts Collection
  //  # from "Tick Timer"
  wire        tt_rdy;
  wire        tt_interrupt_enable;
  //  # from "Programmble Interrupt Controller"
  wire        pic_rdy; // an interrupt
  wire        pic_interrupt_enable;
  //  # flag to enabel/disable exterlal interrupts processing
  //    depending on the fact is instructions restartable or not
  wire        exec_interrupts_en;
  //  # Write-Back latches
  reg         wrbk_tt_interrupt_r;
  reg         wrbk_pic_interrupt_r;


  // Exeptions process:
  wire dcod_op_rfe;
  wire exec_op_rfe;
  reg  wrbk_op_rfe_r;
  wire ctrl_branch_exception;
  wire [OPTION_OPERAND_WIDTH-1:0] ctrl_branch_except_pc;


  // Combined exception/interrupt flag
  wire exec_an_except;
  reg  wrbk_an_except_r;


  //----------------------------//
  // Instruction FETCH instance //
  //----------------------------//

  mor1kx_fetch_marocchino
  #(
    .OPTION_OPERAND_WIDTH             (OPTION_OPERAND_WIDTH), // FETCH
    .OPTION_RF_ADDR_WIDTH             (OPTION_RF_ADDR_WIDTH), // FETCH
    // temporary:
    .OPTION_ORFPX64A32_ABI            (OPTION_ORFPX64A32_ABI), // FETCH
    // branch predictor parameters
    .GSHARE_BITS_NUM                  (GSHARE_BITS_NUM), // FETCH
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
    .cpu_clk                          (cpu_clk), // FETCH
    .cpu_rst                          (cpu_rst), // FETCH

    // pipeline control
    .padv_fetch_i                     (padv_fetch), // FETCH
    .padv_dcod_i                      (padv_dcod), // FETCH
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
    .ibus_burst_last_i                (ibus_burst_last_i), // FETCH
    .ibus_req_o                       (ibus_req_o), // FETCH
    .ibus_adr_o                       (ibus_adr_o), // FETCH
    .ibus_burst_o                     (ibus_burst_o), // FETCH

    // Jump/Branch processing
    //  # jump/branch variants
    .fetch_op_jimm_o                  (fetch_op_jimm), // FETCH
    .fetch_op_jr_o                    (fetch_op_jr), // FETCH
    .fetch_op_bf_o                    (fetch_op_bf), // FETCH
    .fetch_op_bnf_o                   (fetch_op_bnf), // FETCH
    //  # combined jump/branch flag
    .fetch_op_jb_o                    (fetch_op_jb), // FETCH
    //  # "to immediate driven target"
    .fetch_to_imm_target_o            (fetch_to_imm_target), // FETCH
    //  # do branch (pedicted or unconditional)
    .do_branch_i                      (do_branch), // FETCH
    .do_branch_target_i               (do_branch_target), // FETCH
    .jr_gathering_target_i            (jr_gathering_target), // FETCH
    //  # branch prediction support
    .after_ds_target_o                (after_ds_target), // FETCH
    .predict_miss_i                   (predict_miss), // FETCH
    .bc_cnt_value_o                   (bc_cnt_value), // FETCH
    .bc_cnt_radr_o                    (bc_cnt_radr), // FETCH
    .bc_cnt_we_i                      (bc_cnt_we), // FETCH
    .bc_cnt_wdat_i                    (bc_cnt_wdat), // FETCH
    .bc_cnt_wadr_i                    (bc_cnt_wadr), // FETCH
    .bc_hist_taken_i                  (bc_hist_taken), // FETCH

    // DU/exception/rfe control transfer
    .ctrl_branch_exception_i          (ctrl_branch_exception), // FETCH
    .ctrl_branch_except_pc_i          (ctrl_branch_except_pc), // FETCH

    // to RF read
    //  # instruction word valid flag
    .fetch_valid_o                    (fetch_valid), // FETCH
    //  # instruction is in delay slot
    .fetch_delay_slot_o               (fetch_delay_slot), // FETCH
    //  # instruction word itsef
    .fetch_insn_o                     (fetch_insn), // FETCH
    //  # operand addresses
    .fetch_rfa1_adr_o                 (fetch_rfa1_adr), // FETCH
    .fetch_rfb1_adr_o                 (fetch_rfb1_adr), // FETCH
    .fetch_rfa2_adr_o                 (fetch_rfa2_adr), // FETCH
    .fetch_rfb2_adr_o                 (fetch_rfb2_adr), // FETCH
    //  # destiny addresses
    .fetch_rfd1_adr_o                 (fetch_rfd1_adr), // FETCH
    .fetch_rfd2_adr_o                 (fetch_rfd2_adr), // FETCH

    //  Exceptions
    .fetch_except_ibus_err_o          (fetch_except_ibus_err), // FETCH
    .fetch_except_itlb_miss_o         (fetch_except_itlb_miss), // FETCH
    .fetch_except_ipagefault_o        (fetch_except_ipagefault), // FETCH
    .fetch_an_except_o                (fetch_an_except), // FETCH

    // Instruction PC
    .pc_fetch_o                       (pc_fetch) // FETCH
  );


  //-------------------------------//
  // Registers File (GPR) instance //
  //-------------------------------//

  mor1kx_rf_marocchino
  #(
    .OPTION_OPERAND_WIDTH           (OPTION_OPERAND_WIDTH), // RF
    .OPTION_RF_CLEAR_ON_INIT        (OPTION_RF_CLEAR_ON_INIT), // RF
    .OPTION_RF_ADDR_WIDTH           (OPTION_RF_ADDR_WIDTH), // RF
    .NUM_GPRS                       (NUM_GPRS), // RF
    .FEATURE_DEBUGUNIT              (FEATURE_DEBUGUNIT), // RF
    .OPTION_RF_NUM_SHADOW_GPR       (OPTION_RF_NUM_SHADOW_GPR) // RF
  )
  u_rf
  (
    // clocks & resets
    .cpu_clk                          (cpu_clk), // RF
    .cpu_rst                          (cpu_rst), // RF
    // pipeline control signals
    .pipeline_flush_i                 (pipeline_flush), // RF
    .padv_dcod_i                      (padv_dcod), // RF
    // SPR bus
    .spr_bus_addr_i                   (spr_bus_addr_o), // RF
    .spr_bus_stb_i                    (spr_bus_stb_o), // RF
    .spr_bus_we_i                     (spr_bus_we_o), // RF
    .spr_bus_dat_i                    (spr_bus_dat_o), // RF
    .spr_bus_ack_gpr0_o               (spr_bus_ack_gpr0), // RF
    .spr_bus_dat_gpr0_o               (spr_bus_dat_gpr0), // RF
    .spr_bus_ack_gprS_o               (spr_bus_ack_gprS), // RF
    .spr_bus_dat_gprS_o               (spr_bus_dat_gprS), // RF
    // from FETCH
    .fetch_rfa1_adr_i                 (fetch_rfa1_adr), // RF
    .fetch_rfb1_adr_i                 (fetch_rfb1_adr), // RF
    // for FPU64
    .fetch_rfa2_adr_i                 (fetch_rfa2_adr), // RF
    .fetch_rfb2_adr_i                 (fetch_rfb2_adr), // RF
    // from DECODE
    .dcod_immediate_i                 (dcod_immediate), // RF
    .dcod_immediate_sel_i             (dcod_immediate_sel), // RF
    .dcod_rfa1_adr_i                  (dcod_rfa1_adr), // RF
    .dcod_rfb1_adr_i                  (dcod_rfb1_adr), // RF
    .dcod_rfa2_adr_i                  (dcod_rfa2_adr), // RF
    .dcod_rfb2_adr_i                  (dcod_rfb2_adr), // RF
    // from Write-Back
    .wrbk_rfd1_we1h_i                 (wrbk_rfd1_we1h), // RF
    .wrbk_rfd1_we_i                   (wrbk_rfd1_we), // RF
    .wrbk_rfd1_adr_i                  (wrbk_rfd1_adr), // RF
    .wrbk_result1_i                   (wrbk_result1), // RF
    // for FPU64
    .wrbk_rfd2_we1h_i                 (wrbk_rfd2_we1h), // RF
    .wrbk_rfd2_we_i                   (wrbk_rfd2_we), // RF
    .wrbk_rfd2_adr_i                  (wrbk_rfd2_adr), // RF
    .wrbk_result2_i                   (wrbk_result2), // RF
    // Operands
    .dcod_rfa1_o                      (dcod_rfa1), // RF
    .dcod_rfb1_o                      (dcod_rfb1), // RF
    .dcod_rfa2_o                      (dcod_rfa2), // RF
    .dcod_rfb2_o                      (dcod_rfb2), // RF
    // we use adder for l.jl/l.jalr to compute return address: (pc+8)
    .dcod_op_jal_i                    (dcod_op_jal), // RF
    .pc_decode_i                      (pc_decode), // RF
    // Special case for l.jr/l.jalr
    .dcod_rfb1_jr_o                   (dcod_rfb1_jr) // RF
  );


  //--------//
  // DECODE //
  //--------//

  mor1kx_decode_marocchino
  #(
    .OPTION_OPERAND_WIDTH             (OPTION_OPERAND_WIDTH), // DECODE
    .OPTION_RF_ADDR_WIDTH             (OPTION_RF_ADDR_WIDTH), // DECODE
    .FEATURE_PSYNC                    (FEATURE_PSYNC), // DECODE
    .FEATURE_CSYNC                    (FEATURE_CSYNC) // DECODE
  )
  u_decode
  (
    // clocks ans reset
    .cpu_clk                          (cpu_clk), // DECODE
    // pipeline controls
    .padv_dcod_i                      (padv_dcod), // DECODE
    .padv_exec_i                      (padv_exec), // DECODE
    .pipeline_flush_i                 (pipeline_flush), // DECODE
    // from IFETCH
    //  # instruction word valid flag
    .fetch_valid_i                    (fetch_valid), // DECODE
    //  # an exception
    .fetch_an_except_i                (fetch_an_except), // DECODE
    //  # instruction is in delay slot
    .fetch_delay_slot_i               (fetch_delay_slot), // DECODE
    //  # instruction word itsef
    .fetch_insn_i                     (fetch_insn), // DECODE
    //  # operands addresses
    .fetch_rfa1_adr_i                 (fetch_rfa1_adr), // DECODE
    .fetch_rfb1_adr_i                 (fetch_rfb1_adr), // DECODE
    .fetch_rfa2_adr_i                 (fetch_rfa2_adr), // DECODE
    .fetch_rfb2_adr_i                 (fetch_rfb2_adr), // DECODE
    //  # destiny addresses
    .fetch_rfd1_adr_i                 (fetch_rfd1_adr), // DECODE
    .fetch_rfd2_adr_i                 (fetch_rfd2_adr), // DECODE
    // latched instruction word and it's attributes
    .dcod_empty_o                     (dcod_empty), // DECODE
    .dcod_delay_slot_o                (dcod_delay_slot), // DECODE
    // OMAN-to-DECODE hazards
    //  # relative operand A1
    .dcod_rfa1_req_o                  (dcod_rfa1_req), // DECODE
    .dcod_rfa1_adr_o                  (dcod_rfa1_adr), // DECODE
    //  # relative operand B1
    .dcod_rfb1_req_o                  (dcod_rfb1_req), // DECODE
    .dcod_rfb1_adr_o                  (dcod_rfb1_adr), // DECODE
    //  # relative operand A2
    .dcod_rfa2_req_o                  (dcod_rfa2_req), // DECODE
    .dcod_rfa2_adr_o                  (dcod_rfa2_adr), // DECODE
    //  # relative operand B2
    .dcod_rfb2_req_o                  (dcod_rfb2_req), // DECODE
    .dcod_rfb2_adr_o                  (dcod_rfb2_adr), // DECODE
    // destiny D1
    .dcod_rfd1_adr_o                  (dcod_rfd1_adr), // DECODE
    .dcod_rfd1_we_o                   (dcod_rfd1_we), // DECODE
    // destiny D2 (for FPU64)
    .dcod_rfd2_adr_o                  (dcod_rfd2_adr), // DECODE
    .dcod_rfd2_we_o                   (dcod_rfd2_we), // DECODE
    // instruction PC
    .pc_fetch_i                       (pc_fetch), // DECODE
    .pc_decode_o                      (pc_decode), // DECODE
    // IMM
    .dcod_immediate_o                 (dcod_immediate), // DECODE
    .dcod_immediate_sel_o             (dcod_immediate_sel), // DECODE
    // various instruction attributes
    .dcod_flag_we_o                   (dcod_flag_we), // DECODE
    // LSU related
    .dcod_imm16_o                     (dcod_imm16), // DECODE
    .dcod_op_lsu_load_o               (dcod_op_lsu_load), // DECODE
    .dcod_op_lsu_store_o              (dcod_op_lsu_store), // DECODE
    .dcod_op_lsu_atomic_o             (dcod_op_lsu_atomic), // DECODE
    .dcod_lsu_length_o                (dcod_lsu_length), // DECODE
    .dcod_lsu_zext_o                  (dcod_lsu_zext), // DECODE
    .dcod_op_msync_o                  (dcod_op_msync), // DECODE
    .dcod_op_lsu_any_o                (dcod_op_lsu_any), // DECODE
    // Instructions which push EXECUTION without extra conditions
    .dcod_op_push_exec_o              (dcod_op_push_exec), // DECODE
    // Instructions which push WRITE-BACK without extra conditions
    .dcod_op_push_wrbk_o              (dcod_op_push_wrbk), // DECODE
    // 1-clock instruction
    .dcod_op_1clk_o                   (dcod_op_1clk), // DECODE
    // Reqired flag or carry
    .dcod_flag_carry_req_o            (dcod_flag_carry_req), // DECODE
    // Adder related
    .dcod_op_add_o                    (dcod_op_add), // DECODE
    .dcod_adder_do_sub_o              (dcod_adder_do_sub), // DECODE
    .dcod_adder_do_carry_o            (dcod_adder_do_carry), // DECODE
    // Shift
    .dcod_op_shift_o                  (dcod_op_shift), // DECODE
    .dcod_opc_shift_o                 (dcod_opc_shift), // DECODE
    // ffl1
    .dcod_op_ffl1_o                   (dcod_op_ffl1), // DECODE
    .dcod_opc_ffl1_o                  (dcod_opc_ffl1), // DECODE
    // movhi, cmov
    .dcod_op_movhi_o                  (dcod_op_movhi), // DECODE
    .dcod_op_cmov_o                   (dcod_op_cmov), // DECODE
    // extsz
    .dcod_op_extsz_o                  (dcod_op_extsz), // DECODE
    .dcod_opc_extsz_o                 (dcod_opc_extsz), // DECODE
    // Logic
    .dcod_op_logic_o                  (dcod_op_logic), // DECODE
    .dcod_lut_logic_o                 (dcod_lut_logic), // DECODE
    // Jump & Link
    .dcod_op_jal_o                    (dcod_op_jal), // DECODE
    // Set flag related
    .dcod_op_setflag_o                (dcod_op_setflag), // DECODE
    .dcod_opc_setflag_o               (dcod_opc_setflag), // DECODE
    // Multiplier related
    .dcod_op_mul_o                    (dcod_op_mul), // DECODE
    // Divider related
    .dcod_op_div_o                    (dcod_op_div), // DECODE
    .dcod_op_div_signed_o             (dcod_op_div_signed), // DECODE
    .dcod_op_div_unsigned_o           (dcod_op_div_unsigned), // DECODE
    // Combined for MULDIV_RSRVS
    .dcod_op_muldiv_o                 (dcod_op_muldiv), // DECODE
    // FPU-64 arithmetic part
    .dcod_op_fpxx_arith_o             (dcod_op_fpxx_arith), // DECODE
    .dcod_op_fp64_arith_o             (dcod_op_fp64_arith), // DECODE
    .dcod_op_fpxx_add_o               (dcod_op_fpxx_add), // DECODE
    .dcod_op_fpxx_sub_o               (dcod_op_fpxx_sub), // DECODE
    .dcod_op_fpxx_mul_o               (dcod_op_fpxx_mul), // DECODE
    .dcod_op_fpxx_div_o               (dcod_op_fpxx_div), // DECODE
    .dcod_op_fpxx_i2f_o               (dcod_op_fpxx_i2f), // DECODE
    .dcod_op_fpxx_f2i_o               (dcod_op_fpxx_f2i), // DECODE
    // FPU-64 comparison part
    .dcod_op_fpxx_cmp_o               (dcod_op_fpxx_cmp), // DECODE
    .dcod_opc_fpxx_cmp_o              (dcod_opc_fpxx_cmp), // DECODE
    // Combined for FPU_RSRVS
    .dcod_op_fpxx_any_o               (dcod_op_fpxx_any), // DECODE
    // MTSPR / MFSPR
    .dcod_op_mtspr_o                  (dcod_op_mtspr), // DECODE
    .dcod_op_mXspr_o                  (dcod_op_mXspr), // DECODE
    // Exception flags
    //  ## enable l.trap exception
    .du_trap_enable_i                 (du_trap_enable), // DECODE
    //  ## outcome exception flags
    .dcod_except_illegal_o            (dcod_except_illegal), // DECODE
    .dcod_except_syscall_o            (dcod_except_syscall), // DECODE
    .dcod_except_trap_o               (dcod_except_trap), // DECODE
    //  ## combined IFETCH/DECODE an exception flag
    .dcod_an_except_fd_o              (dcod_an_except_fd), // DECODE
    // RFE proc
    .dcod_op_rfe_o                    (dcod_op_rfe) // DECODE
  );


  //-------------------//
  // [O]rder [MAN]ager //
  //-------------------//

  mor1kx_oman_marocchino
  #(
    .OPTION_OPERAND_WIDTH       (OPTION_OPERAND_WIDTH), // OMAN
    .OPTION_RF_ADDR_WIDTH       (OPTION_RF_ADDR_WIDTH), // OMAN
    .NUM_GPRS                   (NUM_GPRS), // OMAN
    .DEST_EXTADR_WIDTH          (DEST_EXTADR_WIDTH), // OMAN
    // branch predictor parameters
    .GSHARE_BITS_NUM            (GSHARE_BITS_NUM) // OMAN
  )
  u_oman
  (
    // clock & reset
    .cpu_clk                    (cpu_clk), // OMAN
    .cpu_rst                    (cpu_rst), // OMAN

    // pipeline control
    .padv_dcod_i                (padv_dcod), // OMAN
    .padv_exec_i                (padv_exec), // OMAN
    .padv_wrbk_i                (padv_wrbk), // OMAN
    .pipeline_flush_i           (pipeline_flush), // OMAN

    // fetched instruction is valid
    .fetch_valid_i              (fetch_valid), // OMAN
    .fetch_delay_slot_i         (fetch_delay_slot), // OMAN

    // for l.jr/l.jalr processing
    .fetch_rfb1_adr_i           (fetch_rfb1_adr), // OMAN

    // DECODE non-latched flags to indicate next required unit
    // (The information is stored in order control buffer)
    .dcod_op_push_wrbk_i        (dcod_op_push_wrbk), // OMAN
    .fetch_op_jb_i              (fetch_op_jb), // OMAN
    .dcod_op_div_i              (dcod_op_div), // OMAN
    .dcod_op_mul_i              (dcod_op_mul), // OMAN
    .dcod_op_fpxx_arith_i       (dcod_op_fpxx_arith), // OMAN
    .dcod_op_ls_i               (dcod_op_lsu_load | dcod_op_lsu_store), // OMAN
    .dcod_op_rfe_i              (dcod_op_rfe), // OMAN
    // for FPU64
    .dcod_op_fpxx_cmp_i         (dcod_op_fpxx_cmp), // OMAN

    // DECODE non-latched additional information related instruction
    //  part #1: iformation stored in order control buffer
    .pc_decode_i                (pc_decode), // OMAN
    .dcod_rfd1_adr_i            (dcod_rfd1_adr), // OMAN
    .dcod_rfd1_we_i             (dcod_rfd1_we), // OMAN
    .dcod_flag_we_i             (dcod_flag_we), // OMAN
    .dcod_delay_slot_i          (dcod_delay_slot), // OMAN
    .dcod_rfd2_adr_i            (dcod_rfd2_adr), // OMAN for FPU64
    .dcod_rfd2_we_i             (dcod_rfd2_we), // OMAN for FPU64
    //  part #2: information required for create enable for
    //           for external (timer/ethernet/uart/etc) interrupts
    .dcod_op_lsu_store_i        (dcod_op_lsu_store), // OMAN
    .dcod_op_msync_i            (dcod_op_msync), // OMAN
    .dcod_op_mXspr_i            (dcod_op_mXspr), // OMAN

    // for unit hazard detection
    .dcod_op_1clk_i             (dcod_op_1clk), // OMAN

    // collect valid flags from execution modules
    .op_1clk_valid_i            (op_1clk_valid), // OMAN
    .div_valid_i                (div_valid), // OMAN
    .mul_valid_i                (mul_valid), // OMAN
    .fpxx_arith_valid_i         (fpxx_arith_valid), // OMAN
    .fpxx_cmp_valid_i           (fpxx_cmp_valid), // OMAN
    .lsu_valid_i                (lsu_valid), // OMAN: result ready or exceptions

    // FETCH & DECODE exceptions
    .fetch_except_ibus_err_i    (fetch_except_ibus_err), // OMAN
    .fetch_except_ipagefault_i  (fetch_except_ipagefault), // OMAN
    .fetch_except_itlb_miss_i   (fetch_except_itlb_miss), // OMAN
    .dcod_except_illegal_i      (dcod_except_illegal), // OMAN
    .dcod_except_syscall_i      (dcod_except_syscall), // OMAN
    .dcod_except_trap_i         (dcod_except_trap), // OMAN
    .dcod_an_except_fd_i        (dcod_an_except_fd), // OMAN

    // OMAN-to-DECODE hazards
    //  # relative operand A1
    .dcod_rfa1_req_i            (dcod_rfa1_req), // OMAN
    .dcod_rfa1_adr_i            (dcod_rfa1_adr), // OMAN
    .omn2dec_hazard_d1a1_o      (omn2dec_hazard_d1a1), // OMAN
    .omn2dec_hazard_d2a1_o      (omn2dec_hazard_d2a1), // OMAN
    .omn2dec_extadr_dxa1_o      (omn2dec_extadr_dxa1), // OMAN
    //  # relative operand B1
    .dcod_rfb1_req_i            (dcod_rfb1_req), // OMAN
    .dcod_rfb1_adr_i            (dcod_rfb1_adr), // OMAN
    .omn2dec_hazard_d1b1_o      (omn2dec_hazard_d1b1), // OMAN
    .omn2dec_hazard_d2b1_o      (omn2dec_hazard_d2b1), // OMAN
    .omn2dec_extadr_dxb1_o      (omn2dec_extadr_dxb1), // OMAN
    //  # relative operand A2
    .dcod_rfa2_req_i            (dcod_rfa2_req), // OMAN
    .dcod_rfa2_adr_i            (dcod_rfa2_adr), // OMAN
    .omn2dec_hazard_d1a2_o      (omn2dec_hazard_d1a2), // OMAN
    .omn2dec_hazard_d2a2_o      (omn2dec_hazard_d2a2), // OMAN
    .omn2dec_extadr_dxa2_o      (omn2dec_extadr_dxa2), // OMAN
    //  # relative operand B2
    .dcod_rfb2_req_i            (dcod_rfb2_req), // OMAN
    .dcod_rfb2_adr_i            (dcod_rfb2_adr), // OMAN
    .omn2dec_hazard_d1b2_o      (omn2dec_hazard_d1b2), // OMAN
    .omn2dec_hazard_d2b2_o      (omn2dec_hazard_d2b2), // OMAN
    .omn2dec_extadr_dxb2_o      (omn2dec_extadr_dxb2), // OMAN

    // support in-1clk-unit forwarding
    .dcod_extadr_o              (dcod_extadr), // OMAN

    // [O]rder [C]ontrol [B]uffer statuses
    .ocb_full_o                 (ocb_full), // OMAN
    .ocb_empty_o                (ocb_empty), // OMAN

    // DECODE result could be processed by EXECUTE
    .dcod_free_o                (dcod_free), // OMAN

    // EXECUTE completed (desired unit is ready)
    .exec_valid_o               (exec_valid), // OMAN

    // control Write-Back latches of execution modules
    .grant_wrbk_to_1clk_o       (grant_wrbk_to_1clk), // OMAN
    .grant_wrbk_to_div_o        (grant_wrbk_to_div), // OMAN
    .grant_wrbk_to_mul_o        (grant_wrbk_to_mul), // OMAN
    .grant_wrbk_to_fpxx_arith_o (grant_wrbk_to_fpxx_arith), // OMAN
    .grant_wrbk_to_lsu_o        (grant_wrbk_to_lsu), // OMAN
    // for FPU64
    .grant_wrbk_to_fpxx_cmp_o   (grant_wrbk_to_fpxx_cmp), // OMAN

    // Logic to support Jump / Branch taking
    //    ## jump/branch variants
    .fetch_op_jimm_i            (fetch_op_jimm), // OMAN
    .fetch_op_jr_i              (fetch_op_jr), // OMAN
    .fetch_op_bf_i              (fetch_op_bf), // OMAN
    .fetch_op_bnf_i             (fetch_op_bnf), // OMAN
    //    ## "to immediate driven target"
    .fetch_to_imm_target_i      (fetch_to_imm_target), // OMAN
    // register target
    .dcod_rfb1_jr_i             (dcod_rfb1_jr), // OMAN
    .wrbk_result1_i             (wrbk_result1), // OMAN
    // comparision flag for l.bf / l.bnf
    .ctrl_flag_sr_i             (ctrl_flag_sr), // OMAN
    // jump/branch signals to IFETCH
    .do_branch_o                (do_branch), // OMAN
    .do_branch_target_o         (do_branch_target), // OMAN
    .jr_gathering_target_o      (jr_gathering_target), // OMAN
    //  # branch prediction support
    .after_ds_target_i          (after_ds_target), // OMAN
    .predict_miss_o             (predict_miss), // OMAN
    .bc_cnt_value_i             (bc_cnt_value), // OMAN
    .bc_cnt_radr_i              (bc_cnt_radr), // OMAN
    .bc_cnt_we_o                (bc_cnt_we), // OMAN
    .bc_cnt_wdat_o              (bc_cnt_wdat), // OMAN
    .bc_cnt_wadr_o              (bc_cnt_wadr), // OMAN
    .bc_hist_taken_o            (bc_hist_taken), // OMAN
    // Support IBUS error handling in CTRL
    .wrbk_jump_or_branch_o      (wrbk_jump_or_branch), // OMAN
    .wrbk_jump_o                (wrbk_jump), // OMAN
    .wrbk_op_bf_o               (wrbk_op_bf), // OMAN
    .wrbk_jb_target_o           (wrbk_jb_target), // OMAN

    //   Flag to enabel/disable exterlal interrupts processing
    // depending on the fact is instructions restartable or not
    .exec_interrupts_en_o       (exec_interrupts_en), // OMAN

    // pre-Write-Back l.rfe
    .exec_op_rfe_o              (exec_op_rfe), // OMAN
    // pre-Write-Back output exceptions: IFETCH
    .exec_except_ibus_err_o     (exec_except_ibus_err), // OMAN
    .exec_except_ipagefault_o   (exec_except_ipagefault), // OMAN
    .exec_except_itlb_miss_o    (exec_except_itlb_miss), // OMAN
    .exec_except_ibus_align_o   (exec_except_ibus_align), // OMAN
    // pre-Write-Back output exceptions: DECODE
    .exec_except_illegal_o      (exec_except_illegal), // OMAN
    .exec_except_syscall_o      (exec_except_syscall), // OMAN
    .exec_except_trap_o         (exec_except_trap), // OMAN
    // pre-Write-Back output exceptions: IFETCH/DECODE
    .exec_an_except_fd_o        (exec_an_except_fd), // OMAN

    // Write-Back outputs
    //  ## special Write-Back-controls for RF
    .wrbk_rfd1_we1h_o           (wrbk_rfd1_we1h), // OMAN
    .wrbk_rfd1_we_o             (wrbk_rfd1_we), // OMAN
    .wrbk_rfd1_adr_o            (wrbk_rfd1_adr), // OMAN
    .wrbk_rfd2_we1h_o           (wrbk_rfd2_we1h), // OMAN
    .wrbk_rfd2_we_o             (wrbk_rfd2_we), // OMAN
    .wrbk_rfd2_adr_o            (wrbk_rfd2_adr), // OMAN
    //  ## instruction related information
    .pc_wrbk_o                  (pc_wrbk), // OMAN
    .pc_nxt_wrbk_o              (pc_nxt_wrbk), // OMAN
    .pc_nxt2_wrbk_o             (pc_nxt2_wrbk), // OMAN
    .wrbk_delay_slot_o          (wrbk_delay_slot), // OMAN
    // for hazards resolution in RSRVS
    .wrbk_extadr_o              (wrbk_extadr) // OMAN
  );


  //--------------------//
  // 1-clock operations //
  //--------------------//

  // instructions per 1-clock sub-unit
  wire                           exec_op_ffl1;
  wire                           exec_op_add;
  wire                           exec_op_shift;
  wire                           exec_op_movhi;
  wire                           exec_op_cmov;
  wire                           exec_op_extsz;
  wire                           exec_op_logic;
  wire                           exec_op_setflag;
  // all of earlier components:
  localparam ONE_CLK_OP_WIDTH = 8;

  //  # attributes
  wire                            exec_flag_carry_req;
  wire                            exec_adder_do_sub;
  wire                            exec_adder_do_carry;
  wire                            exec_opc_ffl1;
  wire                      [3:0] exec_opc_shift; // {SLL, SRL, SRA, ROR}
  wire                      [3:0] exec_opc_extsz; 
  wire                      [3:0] exec_lut_logic;
  wire [`OR1K_COMP_OPC_WIDTH-1:0] exec_opc_setflag;
  // attributes include all of earlier components:
  localparam ONE_CLK_OPC_WIDTH = 16 + `OR1K_COMP_OPC_WIDTH;

  // flags for in-1clk-unit forwarding multiplexors
  wire                            exec_1clk_ff_d1a1;
  wire                            exec_1clk_ff_d1b1;

  // input operands A and B with forwarding from Write-Back
  wire [OPTION_OPERAND_WIDTH-1:0] exec_1clk_a1;
  wire [OPTION_OPERAND_WIDTH-1:0] exec_1clk_b1;

  //  # update carry flag by 1clk-operation
  wire wrbk_1clk_carry_set;
  wire wrbk_1clk_carry_clear;

  //  # update overflow flag by 1clk-operation
  wire wrbk_1clk_overflow_set;
  wire wrbk_1clk_overflow_clear;

  // **** reservation station for 1-clk ****
  mor1kx_rsrvs_1clk_marocchino // 1CLK_RSVRS
  #(
    .OPTION_OPERAND_WIDTH         (OPTION_OPERAND_WIDTH), // 1CLK_RSVRS
    .OP_WIDTH                     (ONE_CLK_OP_WIDTH), // 1CLK_RSVRS
    .OPC_WIDTH                    (ONE_CLK_OPC_WIDTH), // 1CLK_RSVRS
    .DEST_EXTADR_WIDTH            (DEST_EXTADR_WIDTH) // 1CLK_RSVRS
  )
  u_1clk_rsrvs
  (
    // clocks and resets
    .cpu_clk                    (cpu_clk), // 1CLK_RSVRS
    // pipeline control signals in
    .pipeline_flush_i           (pipeline_flush), // 1CLK_RSVRS
    .padv_rsrvs_i               (padv_1clk_rsrvs), // 1CLK_RSVRS
    .taking_op_i                (taking_1clk_op), // 1CLK_RSVRS
    // input data from DECODE
    .dcod_rfxx_i                ({dcod_rfb1, dcod_rfa1}), // 1CLK_RSVRS
    // OMAN-to-DECODE hazards
    //  # hazards flags
    .omn2dec_hazards_flags_i    ({omn2dec_hazard_d2b1, omn2dec_hazard_d1b1, // 1CLK_RSVRS
                                  omn2dec_hazard_d2a1, omn2dec_hazard_d1a1}), // 1CLK_RSVRS
    //  # hasards addresses
    .omn2dec_hazards_addrs_i    ({omn2dec_extadr_dxb1, omn2dec_extadr_dxa1}), // 1CLK_RSVRS
    // support in-1clk-unit forwarding
    .dcod_rfd1_we_i             (dcod_rfd1_we), // 1CLK_RSVRS
    .dcod_extadr_i              (dcod_extadr), // 1CLK_RSVRS
    // Hazard could be resolving
    //  ## write-back attributes
    .wrbk_extadr_i              (wrbk_extadr), // 1CLK_RSVRS
    //  ## forwarding results
    .wrbk_result1_i             (wrbk_result1), // 1CLK_RSVRS
    .wrbk_result2_i             (wrbk_result2), // 1CLK_RSVRS
    // command and its additional attributes
    .dcod_op_i                  ({dcod_op_ffl1, dcod_op_add, dcod_op_shift, dcod_op_movhi, // 1CLK_RSVRS
                                  dcod_op_cmov, dcod_op_extsz, dcod_op_logic, dcod_op_setflag}), // 1CLK_RSVRS
    .dcod_opc_i                 ({dcod_flag_carry_req, // 1CLK_RSVRS
                                  dcod_adder_do_sub, dcod_adder_do_carry, // 1CLK_RSVRS
                                  dcod_opc_ffl1, dcod_opc_shift, dcod_opc_extsz, // 1CLK_RSVRS
                                  dcod_lut_logic, dcod_opc_setflag}), // 1CLK_RSVRS
    // outputs
    //   command and its additional attributes
    .exec_op_any_o              (exec_op_1clk), // 1CLK_RSVRS
    .exec_op_o                  ({exec_op_ffl1, exec_op_add, exec_op_shift, exec_op_movhi, // 1CLK_RSVRS
                                  exec_op_cmov, exec_op_extsz, exec_op_logic, exec_op_setflag}), // 1CLK_RSVRS
    .exec_opc_o                 ({exec_flag_carry_req, // 1CLK_RSVRS
                                  exec_adder_do_sub, exec_adder_do_carry, // 1CLK_RSVRS
                                  exec_opc_ffl1, exec_opc_shift, exec_opc_extsz, // 1CLK_RSVRS
                                  exec_lut_logic, exec_opc_setflag}), // 1CLK_RSVRS
    //   flags for in-1clk-unit forwarding multiplexors
    .exec_1clk_ff_d1a1_o        (exec_1clk_ff_d1a1), // 1CLK_RSVRS
    .exec_1clk_ff_d1b1_o        (exec_1clk_ff_d1b1), // 1CLK_RSVRS
    //   operands
    .exec_rfa1_o                (exec_1clk_a1), // 1CLK_RSVRS
    .exec_rfb1_o                (exec_1clk_b1), // 1CLK_RSVRS
    //   unit-is-busy flag
    .unit_free_o                (op_1clk_free) // 1CLK_RSVRS
  );


  // **** 1clk ****
  mor1kx_exec_1clk_marocchino
  #(
    .OPTION_OPERAND_WIDTH             (OPTION_OPERAND_WIDTH) // 1CLK_EXEC
  )
  u_exec_1clk
  (
    // clocks & resets
    .cpu_clk                          (cpu_clk), // 1CLK_EXEC

    // pipeline controls
    .pipeline_flush_i                 (pipeline_flush), // 1CLK_EXEC
    .padv_wrbk_i                      (padv_wrbk), // 1CLK_EXEC
    .grant_wrbk_to_1clk_i             (grant_wrbk_to_1clk), // 1CLK_EXEC
    .taking_1clk_op_o                 (taking_1clk_op), // 1CLK_EXEC
    .op_1clk_valid_o                  (op_1clk_valid), // 1CLK_EXEC

    // flags for in-1clk-unit forwarding multiplexors
    .exec_1clk_ff_d1a1_i              (exec_1clk_ff_d1a1), // 1CLK_EXEC
    .exec_1clk_ff_d1b1_i              (exec_1clk_ff_d1b1), // 1CLK_EXEC

    // input operands A and B with forwarding from Write-Back
    .exec_1clk_a1_i                   (exec_1clk_a1), // 1CLK_EXEC
    .exec_1clk_b1_i                   (exec_1clk_b1), // 1CLK_EXEC

    // 1-clock instruction auxiliaries
    .carry_i                          (ctrl_carry), // 1CLK_EXEC
    .flag_i                           (ctrl_flag), // 1CLK_EXEC

    // any 1-clock sub-unit
    .exec_op_1clk_i                   (exec_op_1clk), // 1CLK_EXEC
    // Reqired flag or carry
    .exec_flag_carry_req_i            (exec_flag_carry_req), // 1CLK_EXEC
    // adder
    .exec_op_add_i                    (exec_op_add), // 1CLK_EXEC
    .exec_adder_do_sub_i              (exec_adder_do_sub), // 1CLK_EXEC
    .exec_adder_do_carry_i            (exec_adder_do_carry), // 1CLK_EXEC
    // shift
    .exec_op_shift_i                  (exec_op_shift), // 1CLK_EXEC
    .exec_opc_shift_i                 (exec_opc_shift), // 1CLK_EXEC
    // ffl1
    .exec_op_ffl1_i                   (exec_op_ffl1), // 1CLK_EXEC
    .exec_opc_ffl1_i                  (exec_opc_ffl1), // 1CLK_EXEC
    // movhi, cmov
    .exec_op_movhi_i                  (exec_op_movhi), // 1CLK_EXEC
    .exec_op_cmov_i                   (exec_op_cmov), // 1CLK_EXEC
    // extsz
    .exec_op_extsz_i                  (exec_op_extsz), // 1CLK_EXEC
    .exec_opc_extsz_i                 (exec_opc_extsz), // 1CLK_EXEC
    // logic
    .exec_op_logic_i                  (exec_op_logic), // 1CLK_EXEC
    .exec_lut_logic_i                 (exec_lut_logic), // 1CLK_EXEC
    // Write-Back-latched 1-clock arithmetic result
    .wrbk_1clk_result_o               (wrbk_1clk_result), // 1CLK_EXEC
    //  # update carry flag by 1clk-operation
    .wrbk_1clk_carry_set_o            (wrbk_1clk_carry_set), // 1CLK_EXEC
    .wrbk_1clk_carry_clear_o          (wrbk_1clk_carry_clear), // 1CLK_EXEC
    //  # update overflow flag by 1clk-operation
    .wrbk_1clk_overflow_set_o         (wrbk_1clk_overflow_set), // 1CLK_EXEC
    .wrbk_1clk_overflow_clear_o       (wrbk_1clk_overflow_clear), // 1CLK_EXEC
    //  # generate overflow exception by 1clk-operation
    .except_overflow_enable_i         (except_overflow_enable), // 1CLK_EXEC
    .exec_except_overflow_1clk_o      (exec_except_overflow_1clk), // 1CLK_EXEC
    .wrbk_except_overflow_1clk_o      (wrbk_except_overflow_1clk), // 1CLK_EXEC

    // integer comparison flag
    .exec_op_setflag_i                (exec_op_setflag), // 1CLK_EXEC
    .exec_opc_setflag_i               (exec_opc_setflag), // 1CLK_EXEC
    // Write-Back: integer comparison result
    .wrbk_1clk_flag_set_o             (wrbk_1clk_flag_set), // 1CLK_EXEC
    .wrbk_1clk_flag_clear_o           (wrbk_1clk_flag_clear) // 1CLK_EXEC
  );


  //---------------------------------------------//
  // Reservation station for integer MUL/DIV     //
  //   # 32-bits integer multiplier              //
  //   # 32-bits integer divider                 //
  //---------------------------------------------//

  // run integer multiplier / divider
  wire exec_op_mul;
  wire exec_op_div;
  //  # overall:
  localparam MULDIV_OP_WIDTH = 2;

  // OPC layout for integer MUL/DIV
  wire exec_op_div_signed;
  wire exec_op_div_unsigned;
  //  # overall:
  localparam MULDIV_OPC_WIDTH = 2;

  // MUL/DIV input operands
  wire [(OPTION_OPERAND_WIDTH-1):0] exec_muldiv_a1;
  wire [(OPTION_OPERAND_WIDTH-1):0] exec_muldiv_b1;

  //  # MCLK is tacking operands
  wire imul_taking_op, idiv_taking_op;
  wire muldiv_taking_op = imul_taking_op | idiv_taking_op;

  // **** Integer MUL/DIV reservation station instance ****
  mor1kx_rsrvs_marocchino // MULDIV_RSRVS
  #(
    .OPTION_OPERAND_WIDTH         (OPTION_OPERAND_WIDTH), // MULDIV_RSRVS
    .OP_WIDTH                     (MULDIV_OP_WIDTH), // MULDIV_RSRVS
    .OPC_WIDTH                    (MULDIV_OPC_WIDTH), // MULDIV_RSRVS
    .DEST_EXTADR_WIDTH            (DEST_EXTADR_WIDTH), // MULDIV_RSRVS
    // Reservation station is used for LSU
    .RSRVS_LSU                    (0), // MULDIV_RSRVS
    // Reservation station is used for integer MUL/DIV.
    .RSRVS_MULDIV                 (1), // MULDIV_RSRVS
    // Reservation station is used for FPU3264.
    // Extra logic for the A2 and B2 related hazards is generated.
    .RSRVS_FPU                    (0), // MULDIV_RSRVS
    // Packed operands for various reservation stations:
    //  # LSU :   {   x,    x, rfb1, rfa1}
    //  # 1CLK:   {   x,    x, rfb1, rfa1}
    //  # MULDIV: {   x,    x, rfb1, rfa1}
    //  # FPU:    {rfb2, rfa2, rfb1, rfa1}
    .DCOD_RFXX_WIDTH              (2 * OPTION_OPERAND_WIDTH), // MULDIV_RSRVS
    // OMAN-to-DECODE hazard flags layout for various reservation stations:
    //  # LSU :   {   x,    x,     x,    x,  d2b1, d1b1,  d2a1, d1a1 }
    //  # 1CLK:   {   x,    x,     x,    x,  d2b1, d1b1,  d2a1, d1a1 }
    //  # MULDIV: {   x,    x,     x,    x,  d2b1, d1b1,  d2a1, d1a1 }
    //  # FPU:    {d2b2, d1b2,  d2a2, d1a2,  d2b1, d1b1,  d2a1, d1a1 }
    .OMN2DEC_HAZARDS_FLAGS_WIDTH  (4), // MULDIV_RSRVS
    // OMAN-to-DECODE hazard id layout for various reservation stations:
    //  # LSU :   {   x,    x, dxb1, dxa1 }
    //  # 1CLK:   {   x,    x, dxb1, dxa1 }
    //  # MULDIV: {   x,    x, dxb1, dxa1 }
    //  # FPU:    {dxb2, dxa2, dxb1, dxa1 }
    .OMN2DEC_HAZARDS_ADDRS_WIDTH  (2 * DEST_EXTADR_WIDTH) // MULDIV_RSRVS
  )
  u_muldiv_rsrvs
  (
    // clocks and resets
    .cpu_clk                    (cpu_clk), // MULDIV_RSRVS
    // pipeline control signals in
    .pipeline_flush_i           (pipeline_flush), // MULDIV_RSRVS
    .padv_rsrvs_i               (padv_muldiv_rsrvs), // MULDIV_RSRVS
    .taking_op_i                (muldiv_taking_op), // MULDIV_RSRVS
    // input data from DECODE
    .dcod_rfxx_i                ({dcod_rfb1, dcod_rfa1}), // MULDIV_RSRVS
    // OMAN-to-DECODE hazards
    //  # hazards flags
    .omn2dec_hazards_flags_i    ({omn2dec_hazard_d2b1, omn2dec_hazard_d1b1, // MULDIV_RSRVS
                                  omn2dec_hazard_d2a1, omn2dec_hazard_d1a1}), // MULDIV_RSRVS
    //  # hasards addresses
    .omn2dec_hazards_addrs_i    ({omn2dec_extadr_dxb1, omn2dec_extadr_dxa1}), // MULDIV_RSRVS
    // Hazard could be resolving
    //  ## write-back attributes
    .wrbk_extadr_i              (wrbk_extadr), // MULDIV_RSRVS
    //  ## forwarding results
    .wrbk_result1_i             (wrbk_result1), // MULDIV_RSRVS
    .wrbk_result2_i             (wrbk_result2), // MULDIV_RSRVS
    // command and its additional attributes
    .dcod_op_i                  ({dcod_op_mul, dcod_op_div}), // MULDIV_RSRVS
    .dcod_opc_i                 ({dcod_op_div_signed, dcod_op_div_unsigned}),  // MULDIV_RSRVS
    // outputs
    //   command and its additional attributes
    .exec_op_any_o              (), // MULDIV_RSRVS
    .exec_op_o                  ({exec_op_mul, exec_op_div}), // MULDIV_RSRVS
    .exec_opc_o                 ({exec_op_div_signed, exec_op_div_unsigned}),  // MULDIV_RSRVS
    //   operands
    .exec_rfa1_o                (exec_muldiv_a1), // MULDIV_RSRVS
    .exec_rfb1_o                (exec_muldiv_b1), // MULDIV_RSRVS
    .exec_rfa2_o                (), // MULDIV_RSRVS
    .exec_rfb2_o                (), // MULDIV_RSRVS
    //   unit-is-busy flag
    .unit_free_o                (muldiv_free) // MULDIV_RSRVS
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
    .cpu_clk                          (cpu_clk), // MUL
    // pipeline controls
    .pipeline_flush_i                 (pipeline_flush), // MUL
    .padv_wrbk_i                      (padv_wrbk), // MUL
    .grant_wrbk_to_mul_i              (grant_wrbk_to_mul), // MUL
    // input operands from reservation station
    .exec_mul_a1_i                    (exec_muldiv_a1), // MUL
    .exec_mul_b1_i                    (exec_muldiv_b1), // MUL
    //  other inputs/outputs
    .exec_op_mul_i                    (exec_op_mul), // MUL
    .imul_taking_op_o                 (imul_taking_op), // MUL
    .mul_valid_o                      (mul_valid), // MUL
    .wrbk_mul_result_o                (wrbk_mul_result) // MUL
  );


  //----------------//
  // 32-bit divider //
  //----------------//

  //  # update carry flag by division
  wire wrbk_div_carry_set;
  wire wrbk_div_carry_clear;

  //  # update overflow flag by division
  wire wrbk_div_overflow_set;
  wire wrbk_div_overflow_clear;

  // **** integer divider ****
  mor1kx_divider_marocchino
  #(
    .OPTION_OPERAND_WIDTH             (OPTION_OPERAND_WIDTH) // DIV
  )
  u_divider
  (
    // clocks & resets
    .cpu_clk                          (cpu_clk), // DIV
    // pipeline controls
    .pipeline_flush_i                 (pipeline_flush), // DIV
    .padv_wrbk_i                      (padv_wrbk), // DIV
    .grant_wrbk_to_div_i              (grant_wrbk_to_div), // DIV
    // input data from reservation station
    .exec_div_a1_i                    (exec_muldiv_a1), // DIV
    .exec_div_b1_i                    (exec_muldiv_b1), // DIV
    // division command
    .exec_op_div_i                    (exec_op_div), // DIV
    .exec_op_div_signed_i             (exec_op_div_signed), // DIV
    .exec_op_div_unsigned_i           (exec_op_div_unsigned), // DIV
    // division engine state
    .idiv_taking_op_o                 (idiv_taking_op), // DIV
    .div_valid_o                      (div_valid), // DIV
    // write back
    //  # update carry flag by division
    .wrbk_div_carry_set_o             (wrbk_div_carry_set), // DIV
    .wrbk_div_carry_clear_o           (wrbk_div_carry_clear), // DIV
    //  # update overflow flag by division
    .wrbk_div_overflow_set_o          (wrbk_div_overflow_set), // DIV
    .wrbk_div_overflow_clear_o        (wrbk_div_overflow_clear), // DIV
    //  # generate overflow exception by division
    .except_overflow_enable_i         (except_overflow_enable), // DIV
    .exec_except_overflow_div_o       (exec_except_overflow_div), // DIV
    .wrbk_except_overflow_div_o       (wrbk_except_overflow_div), // DIV
    //  # division result
    .wrbk_div_result_o                (wrbk_div_result) // DIV
  );


  //---------------------------------------------//
  // Reservation station for FPU3264             //
  //   # 32/64-bits FP arithmetic                //
  //   # 64-bits FP comparison                   //
  //---------------------------------------------//
  // run fp3264 arithmetic
  wire exec_op_fpxx_add, exec_op_fpxx_sub, exec_op_fpxx_mul,
       exec_op_fpxx_div, exec_op_fpxx_i2f, exec_op_fpxx_f2i;
  // run fp64 comparison
  //(declared earlier)
  //  # overall:
  localparam FPU_OP_WIDTH = 7;

  // OPC layout for multi-clocks reservation station
  wire exec_op_fp64_arith;
  //  # double precision bit:                                1
  //  # fp64 comparison variant:                             3
  //  # ------------------------------------------------------
  //  # overall:                                             4
  localparam FPU_OPC_WIDTH = 4;

  // FPU input operands
  wire [(OPTION_OPERAND_WIDTH-1):0] exec_fpxx_a1;
  wire [(OPTION_OPERAND_WIDTH-1):0] exec_fpxx_b1;
  wire [(OPTION_OPERAND_WIDTH-1):0] exec_fpxx_a2;
  wire [(OPTION_OPERAND_WIDTH-1):0] exec_fpxx_b2;

  // **** FPU3264 reservation station instance ****
  mor1kx_rsrvs_marocchino // FPU_RSRVS
  #(
    .OPTION_OPERAND_WIDTH         (OPTION_OPERAND_WIDTH), // FPU_RSRVS
    .OP_WIDTH                     (FPU_OP_WIDTH), // FPU_RSRVS
    .OPC_WIDTH                    (FPU_OPC_WIDTH), // FPU_RSRVS
    .DEST_EXTADR_WIDTH            (DEST_EXTADR_WIDTH), // FPU_RSRVS
    // Reservation station is used for LSU
    .RSRVS_LSU                    (0), // FPU_RSRVS
    // Reservation station is used for integer MUL/DIV.
    .RSRVS_MULDIV                 (0), // FPU_RSRVS
    // Reservation station is used for FPU3264.
    // Extra logic for the A2 and B2 related hazards is generated.
    .RSRVS_FPU                    (1), // FPU_RSRVS
    // Packed operands for various reservation stations:
    //  # LSU :   {   x,    x, rfb1, rfa1}
    //  # 1CLK:   {   x,    x, rfb1, rfa1}
    //  # MULDIV: {   x,    x, rfb1, rfa1}
    //  # FPU:    {rfb2, rfa2, rfb1, rfa1}
    .DCOD_RFXX_WIDTH              (4 * OPTION_OPERAND_WIDTH), // FPU_RSRVS
    // OMAN-to-DECODE hazard flags layout for various reservation stations:
    //  # LSU :   {   x,    x,     x,    x,  d2b1, d1b1,  d2a1, d1a1 }
    //  # 1CLK:   {   x,    x,     x,    x,  d2b1, d1b1,  d2a1, d1a1 }
    //  # MULDIV: {   x,    x,     x,    x,  d2b1, d1b1,  d2a1, d1a1 }
    //  # FPU:    {d2b2, d1b2,  d2a2, d1a2,  d2b1, d1b1,  d2a1, d1a1 }
    .OMN2DEC_HAZARDS_FLAGS_WIDTH  (8), // FPU_RSRVS
    // OMAN-to-DECODE hazard id layout for various reservation stations:
    //  # LSU :   {   x,    x, dxb1, dxa1 }
    //  # 1CLK:   {   x,    x, dxb1, dxa1 }
    //  # MULDIV: {   x,    x, dxb1, dxa1 }
    //  # FPU:    {dxb2, dxa2, dxb1, dxa1 }
    .OMN2DEC_HAZARDS_ADDRS_WIDTH  (4 * DEST_EXTADR_WIDTH) // FPU_RSRVS
  )
  u_fpxx_rsrvs
  (
    // clocks and resets
    .cpu_clk                    (cpu_clk), // FPU_RSRVS
    // pipeline control signals in
    .pipeline_flush_i           (pipeline_flush), // FPU_RSRVS
    .padv_rsrvs_i               (padv_fpxx_rsrvs), // FPU_RSRVS
    .taking_op_i                (fpxx_taking_op), // FPU_RSRVS
    // input data from DECODE
    .dcod_rfxx_i                ({dcod_rfb2, dcod_rfa2, dcod_rfb1, dcod_rfa1}), // FPU_RSRVS
    // OMAN-to-DECODE hazards
    //  # hazards flags
    .omn2dec_hazards_flags_i    ({omn2dec_hazard_d2b2, omn2dec_hazard_d1b2,  // FPU_RSRVS
                                  omn2dec_hazard_d2a2, omn2dec_hazard_d1a2, // FPU_RSRVS
                                  omn2dec_hazard_d2b1, omn2dec_hazard_d1b1, // FPU_RSRVS
                                  omn2dec_hazard_d2a1, omn2dec_hazard_d1a1}), // FPU_RSRVS
    //  # hasards addresses
    .omn2dec_hazards_addrs_i    ({omn2dec_extadr_dxb2, omn2dec_extadr_dxa2, // FPU_RSRVS
                                  omn2dec_extadr_dxb1, omn2dec_extadr_dxa1}), // FPU_RSRVS
    // Hazard could be resolving
    //  ## write-back attributes
    .wrbk_extadr_i              (wrbk_extadr), // FPU_RSRVS
    //  ## forwarding results
    .wrbk_result1_i             (wrbk_result1), // FPU_RSRVS
    .wrbk_result2_i             (wrbk_result2), // FPU_RSRVS
    // command and its additional attributes
    .dcod_op_i                  ({dcod_op_fpxx_add, dcod_op_fpxx_sub, dcod_op_fpxx_mul, // FPU_RSRVS
                                  dcod_op_fpxx_div, dcod_op_fpxx_i2f, dcod_op_fpxx_f2i, // FPU_RSRVS
                                  dcod_op_fpxx_cmp}), // FPU_RSRVS
    .dcod_opc_i                 ({dcod_op_fp64_arith, dcod_opc_fpxx_cmp}), // FPU_RSRVS
    // outputs
    //   command and its additional attributes
    .exec_op_any_o              (), // FPU_RSRVS
    .exec_op_o                  ({exec_op_fpxx_add, exec_op_fpxx_sub, exec_op_fpxx_mul, // FPU_RSRVS
                                  exec_op_fpxx_div, exec_op_fpxx_i2f, exec_op_fpxx_f2i, // FPU_RSRVS
                                  exec_op_fpxx_cmp}), // FPU_RSRVS
    .exec_opc_o                 ({exec_op_fp64_arith, exec_opc_fpxx_cmp}),  // FPU_RSRVS
    //   operands
    .exec_rfa1_o                (exec_fpxx_a1), // FPU_RSRVS
    .exec_rfb1_o                (exec_fpxx_b1), // FPU_RSRVS
    .exec_rfa2_o                (exec_fpxx_a2), // FPU_RSRVS
    .exec_rfb2_o                (exec_fpxx_b2), // FPU_RSRVS
    //   unit-is-busy flag
    .unit_free_o                (fpxx_free) // FPU_RSRVS
  );


  //---------//
  // FPU3264 //
  //---------//
  pfpu_top_marocchino  u_pfpu3264
  (
    // clock & reset
    .cpu_clk                    (cpu_clk), // FPU3264

    // pipeline control
    .pipeline_flush_i           (pipeline_flush), // FPU3264
    .padv_wrbk_i                (padv_wrbk), // FPU3264
    .grant_wrbk_to_fpxx_arith_i (grant_wrbk_to_fpxx_arith), // FPU3264
    .grant_wrbk_to_fpxx_cmp_i   (grant_wrbk_to_fpxx_cmp), // FPU3264

    // pipeline control outputs
    .fpxx_taking_op_o           (fpxx_taking_op), // FPU3264
    .fpxx_arith_valid_o         (fpxx_arith_valid), // FPU3264
    .fpxx_cmp_valid_o           (fpxx_cmp_valid), // FPU3264

    // Configuration
    .fpu_round_mode_i           (ctrl_fpu_round_mode), // FPU3264
    .except_fpu_enable_i        (except_fpu_enable), // FPU3264
    .fpu_mask_flags_i           (ctrl_fpu_mask_flags), // FPU3264

    // Commands for arithmetic part
    .exec_op_fp64_arith_i       (exec_op_fp64_arith), // FPU3264
    .exec_op_fpxx_add_i         (exec_op_fpxx_add), // FPU3264
    .exec_op_fpxx_sub_i         (exec_op_fpxx_sub), // FPU3264
    .exec_op_fpxx_mul_i         (exec_op_fpxx_mul), // FPU3264
    .exec_op_fpxx_div_i         (exec_op_fpxx_div), // FPU3264
    .exec_op_fpxx_i2f_i         (exec_op_fpxx_i2f), // FPU3264
    .exec_op_fpxx_f2i_i         (exec_op_fpxx_f2i), // FPU3264

    // Commands for comparison part
    .exec_op_fpxx_cmp_i         (exec_op_fpxx_cmp), // FPU3264
    .exec_opc_fpxx_cmp_i        (exec_opc_fpxx_cmp), // FPU3264

    // Operands from reservation station
    .exec_fpxx_a1_i             (exec_fpxx_a1), // FPU3264
    .exec_fpxx_b1_i             (exec_fpxx_b1), // FPU3264
    .exec_fpxx_a2_i             (exec_fpxx_a2), // FPU3264
    .exec_fpxx_b2_i             (exec_fpxx_b2), // FPU3264

    // Pre-Write-Back outputs
    .exec_except_fpxx_arith_o   (exec_except_fpxx_arith), // FPU3264
    .exec_except_fpxx_cmp_o     (exec_except_fpxx_cmp), // FPU3264

    // FPU2364 arithmetic part
    .wrbk_fpxx_arith_res_hi_o   (wrbk_fpxx_arith_res_hi), // FPU3264
    .wrbk_fpxx_arith_res_lo_o   (wrbk_fpxx_arith_res_lo), // FPU3264
    .wrbk_fpxx_arith_fpcsr_o    (wrbk_fpxx_arith_fpcsr), // FPU3264
    .wrbk_fpxx_arith_fpcsr_we_o (wrbk_fpxx_arith_fpcsr_we), // FPU3264
    .wrbk_except_fpxx_arith_o   (wrbk_except_fpxx_arith), // FPU3264

    // FPU-64 comparison part
    .wrbk_fpxx_flag_set_o       (wrbk_fpxx_flag_set), // FPU3264
    .wrbk_fpxx_flag_clear_o     (wrbk_fpxx_flag_clear), // FPU3264
    .wrbk_fpxx_cmp_inv_o        (wrbk_fpxx_cmp_inv), // FPU3264
    .wrbk_fpxx_cmp_inf_o        (wrbk_fpxx_cmp_inf), // FPU3264
    .wrbk_fpxx_cmp_fpcsr_we_o   (wrbk_fpxx_cmp_fpcsr_we), // FPU3264
    .wrbk_except_fpxx_cmp_o     (wrbk_except_fpxx_cmp) // FPU3264
  );


  //--------------//
  // LSU instance //
  //--------------//

  // LSU -> RSRVS feedback
  wire lsu_taking_op;

  // RSRVS -> LSU connections
  //  # combined load/store/msync
  wire                            exec_op_lsu_any;
  //  # particular commands and their attributes
  wire                            exec_op_lsu_load;
  wire                            exec_op_lsu_store;
  wire                            exec_op_msync;
  wire                            exec_op_lsu_atomic;
  wire                      [1:0] exec_lsu_length;
  wire                            exec_lsu_zext;
  //  # immediate offset for address computation
  wire      [`OR1K_IMM_WIDTH-1:0] exec_lsu_imm16;
  //  # Delay slot flag and PC to compute store buffer EPCR
  wire                            exec_lsu_delay_slot;
  wire [OPTION_OPERAND_WIDTH-1:0] exec_lsu_pc;
  //  # operands after frorwarding from Write-Back
  wire [OPTION_OPERAND_WIDTH-1:0] exec_lsu_a1;
  wire [OPTION_OPERAND_WIDTH-1:0] exec_lsu_b1;

  // **** reservation station for LSU ****

  // load/store commands:
  localparam LSU_OP_WIDTH = 2;

  // l.msync and commands attributes:
  //  ## l.msync                                 1
  //  ## atomic operation:                       1
  //  ## length:                                 2
  //  ## zero extension:                         1
  //  ## immediate width:                       16
  //  ## delay slot flag                         1
  //  ## PC to compute store buffer EPCR:       32
  localparam LSU_OPC_WIDTH = 6 + `OR1K_IMM_WIDTH + OPTION_OPERAND_WIDTH;

  // reservation station instance
  mor1kx_rsrvs_marocchino // LSU_RSRVS
  #(
    .OPTION_OPERAND_WIDTH         (OPTION_OPERAND_WIDTH), // LSU_RSRVS
    .OP_WIDTH                     (LSU_OP_WIDTH), // LSU_RSRVS
    .OPC_WIDTH                    (LSU_OPC_WIDTH), // LSU_RSRVS
    .DEST_EXTADR_WIDTH            (DEST_EXTADR_WIDTH), // LSU_RSRVS
    // Reservation station is used for LSU
    .RSRVS_LSU                    (1), // LSU_RSRVS
    // Reservation station is used for integer MUL/DIV.
    .RSRVS_MULDIV                 (0), // LSU_RSRVS
    // Reservation station is used for FPU3264.
    // Extra logic for the A2 and B2 related hazards is generated.
    .RSRVS_FPU                    (0), // LSU_RSRVS
    // Packed operands for various reservation stations:
    //  # LSU :   {   x,    x, rfb1, rfa1}
    //  # 1CLK:   {   x,    x, rfb1, rfa1}
    //  # MULDIV: {   x,    x, rfb1, rfa1}
    //  # FPU:    {rfb2, rfa2, rfb1, rfa1}
    .DCOD_RFXX_WIDTH              (2 * OPTION_OPERAND_WIDTH), // LSU_RSRVS
    // OMAN-to-DECODE hazard flags layout for various reservation stations:
    //  # LSU :   {   x,    x,     x,    x,  d2b1, d1b1,  d2a1, d1a1 }
    //  # 1CLK:   {   x,    x,     x,    x,  d2b1, d1b1,  d2a1, d1a1 }
    //  # MULDIV: {   x,    x,     x,    x,  d2b1, d1b1,  d2a1, d1a1 }
    //  # FPU:    {d2b2, d1b2,  d2a2, d1a2,  d2b1, d1b1,  d2a1, d1a1 }
    .OMN2DEC_HAZARDS_FLAGS_WIDTH  (4), // LSU_RSRVS
    // OMAN-to-DECODE hazard id layout for various reservation stations:
    //  # LSU :   {   x,    x, dxb1, dxa1 }
    //  # 1CLK:   {   x,    x, dxb1, dxa1 }
    //  # MULDIV: {   x,    x, dxb1, dxa1 }
    //  # FPU:    {dxb2, dxa2, dxb1, dxa1 }
    .OMN2DEC_HAZARDS_ADDRS_WIDTH  (2 * DEST_EXTADR_WIDTH) // LSU_RSRVS
  )
  u_lsu_rsrvs
  (
    // clocks and resets
    .cpu_clk                    (cpu_clk), // LSU_RSVRS
    // pipeline control signals in
    .pipeline_flush_i           (pipeline_flush), // LSU_RSVRS
    .padv_rsrvs_i               (padv_lsu_rsrvs), // LSU_RSVRS
    .taking_op_i                (lsu_taking_op), // LSU_RSVRS
    // input data from DECODE
    .dcod_rfxx_i                ({dcod_rfb1, dcod_rfa1}), // LSU_RSVRS
    // OMAN-to-DECODE hazards
    //  # hazards flags
    .omn2dec_hazards_flags_i    ({omn2dec_hazard_d2b1, omn2dec_hazard_d1b1, // LSU_RSVRS
                                  omn2dec_hazard_d2a1, omn2dec_hazard_d1a1}), // LSU_RSVRS
    //  # hasards addresses
    .omn2dec_hazards_addrs_i    ({omn2dec_extadr_dxb1, omn2dec_extadr_dxa1}), // LSU_RSVRS
    // Hazard could be resolving
    //  ## write-back attributes
    .wrbk_extadr_i              (wrbk_extadr), // LSU_RSVRS
    //  ## forwarding results
    .wrbk_result1_i             (wrbk_result1), // LSU_RSVRS
    .wrbk_result2_i             (wrbk_result2), // LSU_RSVRS
    // command and its additional attributes
    .dcod_op_i                  ({dcod_op_lsu_load, dcod_op_lsu_store}), // LSU_RSVRS
    .dcod_opc_i                 ({dcod_op_msync,    dcod_op_lsu_atomic, // LSU_RSVRS
                                  dcod_lsu_length,  dcod_lsu_zext, // LSU_RSVRS
                                  dcod_imm16, // LSU_RSVRS
                                  dcod_delay_slot,  pc_decode}), // LSU_RSVRS
    // outputs
    //   command and its additional attributes
    .exec_op_any_o              (exec_op_lsu_any), // LSU_RSVRS
    .exec_op_o                  ({exec_op_lsu_load, exec_op_lsu_store}), // LSU_RSVRS
    .exec_opc_o                 ({exec_op_msync,    exec_op_lsu_atomic, // LSU_RSVRS
                                  exec_lsu_length,  exec_lsu_zext, // LSU_RSVRS
                                  exec_lsu_imm16, // LSU_RSVRS
                                  exec_lsu_delay_slot, exec_lsu_pc}), // LSU_RSVRS
    //   operands
    .exec_rfa1_o                (exec_lsu_a1), // LSU_RSVRS
    .exec_rfb1_o                (exec_lsu_b1), // LSU_RSVRS
    //  ## for FPU64
    .exec_rfa2_o                (), // LSU_RSVRS
    .exec_rfb2_o                (), // LSU_RSVRS
    //   unit-is-busy flag
    .unit_free_o                (lsu_free) // LSU_RSVRS
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
    .cpu_clk                          (cpu_clk), // LSU
    .cpu_rst                          (cpu_rst), // LSU
    // Pipeline controls
    .pipeline_flush_i                 (pipeline_flush), // LSU
    .padv_wrbk_i                      (padv_wrbk), // LSU
    .grant_wrbk_to_lsu_i              (grant_wrbk_to_lsu), // LSU
    // configuration
    .dc_enable_i                      (dc_enable), // LSU
    .dmmu_enable_i                    (dmmu_enable), // LSU
    .supervisor_mode_i                (supervisor_mode), // LSU
    // Input from RSRVR
    .exec_op_lsu_any_i                (exec_op_lsu_any), //LSU
    .exec_op_lsu_load_i               (exec_op_lsu_load), // LSU
    .exec_op_lsu_store_i              (exec_op_lsu_store), // LSU
    .exec_op_msync_i                  (exec_op_msync), // LSU
    .exec_op_lsu_atomic_i             (exec_op_lsu_atomic), // LSU
    .exec_lsu_length_i                (exec_lsu_length), // LSU
    .exec_lsu_zext_i                  (exec_lsu_zext), // LSU
    .exec_lsu_imm16_i                 (exec_lsu_imm16), // LSU
    .exec_lsu_delay_slot_i            (exec_lsu_delay_slot), // LSU (for store buffer EPCR computation)
    .exec_lsu_pc_i                    (exec_lsu_pc), // LSU (for store buffer EPCR computation)
    .exec_lsu_a1_i                    (exec_lsu_a1), // LSU
    .exec_lsu_b1_i                    (exec_lsu_b1), // LSU
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
    .dbus_dat_i                       (dbus_dat_i), // LSU
    .dbus_burst_last_i                (dbus_burst_last_i), // LSU
    .dbus_adr_o                       (dbus_adr_o), // LSU
    .dbus_req_o                       (dbus_req_o), // LSU
    .dbus_dat_o                       (dbus_dat_o), // LSU
    .dbus_bsel_o                      (dbus_bsel_o[3:0]), // LSU
    .dbus_lwa_cmd_o                   (dbus_lwa_cmd_o), // LSU: atomic load
    .dbus_stna_cmd_o                  (dbus_stna_cmd_o), // LSU: none-atomic store
    .dbus_swa_cmd_o                   (dbus_swa_cmd_o), // LSU: atomic store
    .dbus_burst_o                     (dbus_burst_o), // LSU
    // Other connections for lwa/swa support
    .dbus_atomic_flg_i                (dbus_atomic_flg_i), // LSU
    // Cache sync for multi-core environment
    .snoop_adr_i                      (snoop_adr_i[31:0]), // LSU
    .snoop_en_i                       (snoop_en_i), // LSU
    // Pipe control output flags
    .lsu_taking_op_o                  (lsu_taking_op), // LSU
    .lsu_valid_o                      (lsu_valid), // LSU: result ready or exceptions
    // Imprecise exception (with appropriate PC) came via the store buffer
    .sbuf_eear_o                      (sbuf_eear), // LSU
    .sbuf_epcr_o                      (sbuf_epcr), // LSU
    .sbuf_err_o                       (sbuf_err), // LSU
    //  Pre-WriteBack "an exception" flag
    .exec_an_except_lsu_o             (exec_an_except_lsu), // LSU
    // WriteBack load  result
    .wrbk_lsu_result_o                (wrbk_lsu_result), // LSU
    // Atomic operation flag set/clear logic
    .wrbk_atomic_flag_set_o           (wrbk_atomic_flag_set), // LSU
    .wrbk_atomic_flag_clear_o         (wrbk_atomic_flag_clear), // LSU
    // Exceptions & errors
    .wrbk_except_dbus_err_o           (wrbk_except_dbus_err), // LSU
    .wrbk_except_dpagefault_o         (wrbk_except_dpagefault), // LSU
    .wrbk_except_dtlb_miss_o          (wrbk_except_dtlb_miss), // LSU
    .wrbk_except_dbus_align_o         (wrbk_except_dbus_align), // LSU
    .wrbk_lsu_except_addr_o           (wrbk_lsu_except_addr) // LSU:
  );


  //-------------------//
  // Write-Back:result //
  //-------------------//

  // --- regular ---
  always @(wrbk_1clk_result       or wrbk_div_result or wrbk_mul_result or
           wrbk_fpxx_arith_res_hi or wrbk_lsu_result or wrbk_mfspr_result)
  begin
    wrbk_result1 = wrbk_1clk_result       | wrbk_div_result | wrbk_mul_result |
                   wrbk_fpxx_arith_res_hi | wrbk_lsu_result | wrbk_mfspr_result;
  end

  // --- FPU64 extention ---
  assign wrbk_result2 = wrbk_fpxx_arith_res_lo;


  //------------------------------------//
  // Exceptions and External Interrupts //
  //------------------------------------//

  // --- exceptions ---
  assign exec_an_except = exec_an_except_fd        | exec_except_ibus_align    |  // EXEC-AN-EXCEPT
                          exec_except_overflow_div | exec_except_overflow_1clk |  // EXEC-AN-EXCEPT
                          exec_except_fpxx_cmp     | exec_except_fpxx_arith    |  // EXEC-AN-EXCEPT
                          exec_an_except_lsu       | sbuf_err                  |  // EXEC-AN-EXCEPT
                          exec_tt_interrupt        | exec_pic_interrupt;          // EXEC-AN-EXCEPT

  // --- external interrupts ---
  wire exec_tt_interrupt  = tt_rdy  & tt_interrupt_enable  & exec_interrupts_en; // from "Tick Timer"
  wire exec_pic_interrupt = pic_rdy & pic_interrupt_enable & exec_interrupts_en; // from "Programmble Interrupt Controller"

  // --- Write-Back latches ---
  always @(posedge cpu_clk) begin
    if (padv_wrbk) begin  // Write-Back: Exceptions and External Interrupts
      // IFETCH exceptions
      wrbk_except_ibus_err_r   <= exec_except_ibus_err; // Write-Back update
      wrbk_except_ipagefault_r <= exec_except_ipagefault; // Write-Back update
      wrbk_except_itlb_miss_r  <= exec_except_itlb_miss; // Write-Back update
      wrbk_except_ibus_align_r <= exec_except_ibus_align; // Write-Back update
      // DECODE exceptions
      wrbk_except_illegal_r    <= exec_except_illegal; // Write-Back update
      wrbk_except_syscall_r    <= exec_except_syscall; // Write-Back update
      wrbk_except_trap_r       <= exec_except_trap; // Write-Back update
      // External Interrupts
      wrbk_tt_interrupt_r      <= exec_tt_interrupt; // Write-Back update
      wrbk_pic_interrupt_r     <= exec_pic_interrupt; // Write-Back update
      // Combined exceptions/interrupts flag
      wrbk_an_except_r         <= exec_an_except; // Write-Back update
      // RFE
      wrbk_op_rfe_r            <= exec_op_rfe; // Write-Back update
    end
    else begin
      // IFETCH exceptions
      wrbk_except_ibus_err_r   <= 1'b0; // 1-clk-length
      wrbk_except_ipagefault_r <= 1'b0; // 1-clk-length
      wrbk_except_itlb_miss_r  <= 1'b0; // 1-clk-length
      wrbk_except_ibus_align_r <= 1'b0; // 1-clk-length
      // DECODE exceptions
      wrbk_except_illegal_r    <= 1'b0; // 1-clk-length
      wrbk_except_syscall_r    <= 1'b0; // 1-clk-length
      wrbk_except_trap_r       <= 1'b0; // 1-clk-length
      // External Interrupts
      wrbk_tt_interrupt_r      <= 1'b0; // 1-clk-length
      wrbk_pic_interrupt_r     <= 1'b0; // 1-clk-length
      // Combined exceptions/interrupts flag
      wrbk_an_except_r         <= 1'b0; // 1-clk-length
      // RFE
      wrbk_op_rfe_r            <= 1'b0; // 1-clk-length
    end
  end // @clock


  //-------//
  // TIMER //
  //-------//
  //  # connection wires
  wire [31:0] spr_bus_dat_tt;
  wire        spr_bus_ack_tt;
  //  # timer instance
  mor1kx_ticktimer_marocchino
  u_ticktimer
  (
    // Wishbone clock and reset
    .wb_clk             (wb_clk), // TIMER
    .wb_rst             (wb_rst), // TIMER
    // CPU clock and reset
    .cpu_clk            (cpu_clk), // TIMER
    .cpu_rst            (cpu_rst), // TIMER
    // ready flag
    .tt_rdy_o           (tt_rdy), // TIMER
    // SPR interface
    .spr_bus_addr_i     (spr_bus_addr_o), // TIMER
    .spr_bus_we_i       (spr_bus_we_o), // TIMER
    .spr_bus_stb_i      (spr_bus_stb_o), // TIMER
    .spr_bus_toggle_i   (spr_bus_toggle), // TIMER
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
  mor1kx_pic_marocchino
  #(
    .OPTION_PIC_TRIGGER   (OPTION_PIC_TRIGGER), // PIC
    .OPTION_PIC_NMI_WIDTH (OPTION_PIC_NMI_WIDTH) // PIC
  )
  u_pic
  (
    // Wishbone clock and reset
    .wb_clk             (wb_clk), // PIC
    .wb_rst             (wb_rst), // PIC
    // CPU clock and reset
    .cpu_clk            (cpu_clk), // PIC
    .cpu_rst            (cpu_rst), // PIC
    // input interrupt lines
    .irq_i              (irq_i), // PIC
    // output interrupt lines
    .pic_rdy_o          (pic_rdy), // PIC
    // SPR BUS
    //  # inputs
    .spr_bus_addr_i     (spr_bus_addr_o), // PIC
    .spr_bus_we_i       (spr_bus_we_o), // PIC
    .spr_bus_stb_i      (spr_bus_stb_o), // PIC
    .spr_bus_toggle_i   (spr_bus_toggle), // PIC
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
    .FEATURE_MULTICORE          (FEATURE_MULTICORE), // CTRL
    .OPTION_RF_NUM_SHADOW_GPR   (OPTION_RF_NUM_SHADOW_GPR) // CTRL
  )
  u_ctrl
  (
    // clocks & resets
    .cpu_clk                          (cpu_clk), // CTRL
    .cpu_rst                          (cpu_rst), // CTRL

    // Inputs / Outputs for pipeline control signals
    .padv_fetch_o                     (padv_fetch), // CTRL
    .dcod_empty_i                     (dcod_empty), // CTRL
    .dcod_free_i                      (dcod_free), // CTRL
    .ocb_full_i                       (ocb_full), // CTRL
    .ocb_empty_i                      (ocb_empty), // CTRL
    .dcod_op_1clk_i                   (dcod_op_1clk), // CTRL
    .op_1clk_free_i                   (op_1clk_free), // CTRL
    .padv_1clk_rsrvs_o                (padv_1clk_rsrvs), // CTRL
    .dcod_op_muldiv_i                 (dcod_op_muldiv), // CTRL
    .muldiv_free_i                    (muldiv_free), // CTRL
    .padv_muldiv_rsrvs_o              (padv_muldiv_rsrvs), // CTRL
    .dcod_op_fpxx_any_i               (dcod_op_fpxx_any), // CTRL
    .fpxx_free_i                      (fpxx_free), // CTRL
    .padv_fpxx_rsrvs_o                (padv_fpxx_rsrvs), // CTRL
    .dcod_op_lsu_any_i                (dcod_op_lsu_any), // CTRL
    .lsu_free_i                       (lsu_free), // CTRL
    .padv_lsu_rsrvs_o                 (padv_lsu_rsrvs), // CTRL
    .dcod_op_push_exec_i              (dcod_op_push_exec), // CTRL
    .padv_dcod_o                      (padv_dcod), // CTRL
    .padv_exec_o                      (padv_exec), // CTRL
    .exec_valid_i                     (exec_valid), // CTRL
    .padv_wrbk_o                      (padv_wrbk), // CTRL
    .pipeline_flush_o                 (pipeline_flush), // CTRL

    // MF(T)SPR coomand processing
    //  ## iput data & command from DECODE
    .dcod_rfa1_i                      (dcod_rfa1[`OR1K_IMM_WIDTH-1:0]), // CTRL: base of addr for MT(F)SPR
    .dcod_imm16_i                     (dcod_imm16), // CTRL: offset for addr for MT(F)SPR
    .dcod_rfb1_i                      (dcod_rfb1), // CTRL: data for MTSPR
    .dcod_op_mtspr_i                  (dcod_op_mtspr), // CTRL
    .dcod_op_mXspr_i                  (dcod_op_mXspr), // CTRL
    //  ## result to WRBK_MUX
    .wrbk_mfspr_result_o              (wrbk_mfspr_result), // CTRL: for WRBK_MUX

    // Support IBUS error handling in CTRL
    .wrbk_jump_or_branch_i            (wrbk_jump_or_branch), // CTRL
    .wrbk_jump_i                      (wrbk_jump), // CTRL
    .wrbk_op_bf_i                     (wrbk_op_bf), // CTRL
    .wrbk_jb_target_i                 (wrbk_jb_target), // CTRL

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
    .spr_bus_toggle_o                 (spr_bus_toggle), // CTRL
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
    .spr_bus_dat_gpr0_i               (spr_bus_dat_gpr0), // CTRL
    .spr_bus_ack_gpr0_i               (spr_bus_ack_gpr0), // CTRL
    .spr_bus_dat_gprS_i               (spr_bus_dat_gprS), // CTRL
    .spr_bus_ack_gprS_i               (spr_bus_ack_gprS), // CTRL

    // Write-Back: External Interrupt Collection
    .tt_interrupt_enable_o            (tt_interrupt_enable), // CTRL
    .pic_interrupt_enable_o           (pic_interrupt_enable), // CTRL
    .wrbk_tt_interrupt_i              (wrbk_tt_interrupt_r), // CTRL
    .wrbk_pic_interrupt_i             (wrbk_pic_interrupt_r), // CTRL

    // Write-Back: programm counter
    .pc_wrbk_i                        (pc_wrbk), // CTRL
    .pc_nxt_wrbk_i                    (pc_nxt_wrbk), // CTRL
    .pc_nxt2_wrbk_i                   (pc_nxt2_wrbk), // CTRL

    // Write-Back: flag
    .wrbk_1clk_flag_set_i             (wrbk_1clk_flag_set), // CTRL
    .wrbk_1clk_flag_clear_i           (wrbk_1clk_flag_clear), // CTRL
    .wrbk_fpxx_flag_set_i             (wrbk_fpxx_flag_set), // CTRL
    .wrbk_fpxx_flag_clear_i           (wrbk_fpxx_flag_clear), // CTRL
    .wrbk_atomic_flag_set_i           (wrbk_atomic_flag_set), // CTRL
    .wrbk_atomic_flag_clear_i         (wrbk_atomic_flag_clear), // CTRL

    // Write-Back: carry
    .wrbk_div_carry_set_i             (wrbk_div_carry_set), // CTRL
    .wrbk_div_carry_clear_i           (wrbk_div_carry_clear), // CTRL
    .wrbk_1clk_carry_set_i            (wrbk_1clk_carry_set), // CTRL
    .wrbk_1clk_carry_clear_i          (wrbk_1clk_carry_clear), // CTRL

    // Write-Back: overflow
    .wrbk_div_overflow_set_i          (wrbk_div_overflow_set), // CTRL
    .wrbk_div_overflow_clear_i        (wrbk_div_overflow_clear), // CTRL
    .wrbk_1clk_overflow_set_i         (wrbk_1clk_overflow_set), // CTRL
    .wrbk_1clk_overflow_clear_i       (wrbk_1clk_overflow_clear), // CTRL

    //  # FPX3264 arithmetic part
    .wrbk_fpxx_arith_fpcsr_i          (wrbk_fpxx_arith_fpcsr), // CTRL
    .wrbk_fpxx_arith_fpcsr_we_i       (wrbk_fpxx_arith_fpcsr_we), // CTRL
    .wrbk_except_fpxx_arith_i         (wrbk_except_fpxx_arith), // CTRL
    //  # FPX64 comparison part
    .wrbk_fpxx_cmp_inv_i              (wrbk_fpxx_cmp_inv), // CTRL
    .wrbk_fpxx_cmp_inf_i              (wrbk_fpxx_cmp_inf), // CTRL
    .wrbk_fpxx_cmp_fpcsr_we_i         (wrbk_fpxx_cmp_fpcsr_we), // CTRL
    .wrbk_except_fpxx_cmp_i           (wrbk_except_fpxx_cmp), // CTRL

    //  # Excepion processing auxiliaries
    .sbuf_eear_i                      (sbuf_eear), // CTRL
    .sbuf_epcr_i                      (sbuf_epcr), // CTRL
    .sbuf_err_i                       (sbuf_err), // CTRL
    .wrbk_delay_slot_i                (wrbk_delay_slot), // CTRL

    //  # combined exceptions/interrupt flag
    .exec_an_except_i                 (exec_an_except), // CTRL
    .wrbk_an_except_i                 (wrbk_an_except_r), // CTRL

    //  # particular IFETCH exception flags
    .wrbk_except_ibus_err_i           (wrbk_except_ibus_err_r), // CTRL
    .wrbk_except_itlb_miss_i          (wrbk_except_itlb_miss_r), // CTRL
    .wrbk_except_ipagefault_i         (wrbk_except_ipagefault_r), // CTRL
    .wrbk_except_ibus_align_i         (wrbk_except_ibus_align_r), // CTRL

    //  # particular DECODE exception flags
    .wrbk_except_illegal_i            (wrbk_except_illegal_r), // CTRL
    .wrbk_except_syscall_i            (wrbk_except_syscall_r), // CTRL
    .wrbk_except_trap_i               (wrbk_except_trap_r), // CTRL

    //  # particular LSU exception flags
    .wrbk_except_dbus_err_i           (wrbk_except_dbus_err), // CTRL
    .wrbk_except_dtlb_miss_i          (wrbk_except_dtlb_miss), // CTRL
    .wrbk_except_dpagefault_i         (wrbk_except_dpagefault), // CTRL
    .wrbk_except_dbus_align_i         (wrbk_except_dbus_align), // CTRL
    .wrbk_lsu_except_addr_i           (wrbk_lsu_except_addr), // CTRL

    //  # overflow exception processing
    .except_overflow_enable_o         (except_overflow_enable), // CTRL
    .wrbk_except_overflow_div_i       (wrbk_except_overflow_div), // CTRL
    .wrbk_except_overflow_1clk_i      (wrbk_except_overflow_1clk), // CTRL

    //  # Branch to exception/rfe processing address
    .ctrl_branch_exception_o          (ctrl_branch_exception), // CTRL
    .ctrl_branch_except_pc_o          (ctrl_branch_except_pc), // CTRL
    //  # l.rfe
    .exec_op_rfe_i                    (exec_op_rfe), // CTRL
    .wrbk_op_rfe_i                    (wrbk_op_rfe_r), // CTRL

    // Multicore related
    .multicore_coreid_i               (multicore_coreid_i), // CTRL
    .multicore_numcores_i             (multicore_numcores_i), // CTRL

    // Flag & Carry
    .ctrl_flag_o                      (ctrl_flag), // CTRL
    .ctrl_flag_sr_o                   (ctrl_flag_sr), // CTRL
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

endmodule // mor1kx_cpu_marocchino
