////////////////////////////////////////////////////////////////////////
//                                                                    //
//  mor1kx_ctrl_marocchino                                            //
//                                                                    //
//  Description:                                                      //
//    mor1kx control unit for MAROCCHINO pipeline                     //
//      a) generate pipeline controls                                 //
//      b) manage SPRs                                                //
//      c) issue addresses for exceptions to fetch stage              //
//         control branches going to fetch stage                      //
//      d) contains tick timer & PIC logic                            //
//                                                                    //
//  Derived from mor1kx_ctrl_cappuccino.                              //
//                                                                    //
////////////////////////////////////////////////////////////////////////
//                                                                    //
//   Copyright (C) 2012 Julius Baxter                                 //
//                      juliusbaxter@gmail.com                        //
//                                                                    //
//   Copyright (C) 2012-2013 Stefan Kristiansson                      //
//                           stefan.kristiansson@saunalahti.fi        //
//                                                                    //
//   Copyright (C) 2015 Andrey Bacherov                               //
//                      avbacherov@opencores.org                      //
//                                                                    //
//      This Source Code Form is subject to the terms of the          //
//      Open Hardware Description License, v. 1.0. If a copy          //
//      of the OHDL was not distributed with this file, You           //
//      can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt       //
//                                                                    //
////////////////////////////////////////////////////////////////////////

`include "mor1kx-defines.v"

module mor1kx_ctrl_marocchino
#(
  parameter OPTION_OPERAND_WIDTH      = 32,
  parameter OPTION_RESET_PC           = {{(OPTION_OPERAND_WIDTH-13){1'b0}},
                                          `OR1K_RESET_VECTOR,8'd0},

  parameter OPTION_DCACHE_BLOCK_WIDTH = 5,
  parameter OPTION_DCACHE_SET_WIDTH   = 9,
  parameter OPTION_DCACHE_WAYS        = 2,

  parameter OPTION_DMMU_SET_WIDTH     = 6,
  parameter OPTION_DMMU_WAYS          = 1,

  parameter OPTION_ICACHE_BLOCK_WIDTH = 5,
  parameter OPTION_ICACHE_SET_WIDTH   = 9,
  parameter OPTION_ICACHE_WAYS        = 2,

  parameter OPTION_IMMU_SET_WIDTH     = 6,
  parameter OPTION_IMMU_WAYS          = 1,

  parameter FEATURE_DEBUGUNIT         = "NONE",
  parameter FEATURE_PERFCOUNTERS      = "NONE",
  parameter FEATURE_PMU               = "NONE",
  parameter FEATURE_MAC               = "NONE",
  parameter FEATURE_MULTICORE         = "NONE",

  parameter OPTION_PIC_TRIGGER        = "LEVEL",

  parameter SPR_SR_WIDTH              = 16,
  parameter SPR_SR_RESET_VALUE        = 16'h8001
)
(
  input                                 clk,
  input                                 rst,

  // Inputs / Outputs for pipeline control signals
  input                                 dcod_insn_valid_i,
  input                                 fetch_an_except_i,
  input                                 oman_fd_an_except_i,
  input                                 dcod_valid_i,
  input                                 exec_valid_i,
  output reg                            pipeline_flush_o,
  output                                padv_fetch_o,
  output                                padv_decode_o,
  output                                padv_wb_o,

  // MF(T)SPR coomand processing
  //  ## iput data and command from DECODE
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_rfa1_i, // part of addr for MT(F)SPR
  input           [`OR1K_IMM_WIDTH-1:0] dcod_imm16_i, // part of addr for MT(F)SPR
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_rfb1_i, // data for MTSPR
  input                                 dcod_op_mfspr_i,
  input                                 dcod_op_mtspr_i,
  //  ## result to WB_MUX
  output reg [OPTION_OPERAND_WIDTH-1:0] wb_mfspr_dat_o,

  // Support IBUS error handling in CTRL
  input                                 wb_jump_or_branch_i,
  input                                 wb_do_branch_i,
  input      [OPTION_OPERAND_WIDTH-1:0] wb_do_branch_target_i,

  // Debug System accesses CPU SPRs through DU
  input                          [15:0] du_addr_i,
  input                                 du_stb_i,
  input      [OPTION_OPERAND_WIDTH-1:0] du_dat_i,
  input                                 du_we_i,
  output     [OPTION_OPERAND_WIDTH-1:0] du_dat_o,
  output reg                            du_ack_o,
  // Stall control from debug interface
  input                                 du_stall_i,
  output                                du_stall_o,
  // Enable l.trap exception
  output                                du_trap_enable_o,

  // SPR accesses to external units (cache, mmu, etc.)
  output reg                     [15:0] spr_bus_addr_o,
  output reg                            spr_bus_we_o,
  output reg                            spr_bus_stb_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_dc_i,
  input                                 spr_bus_ack_dc_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_ic_i,
  input                                 spr_bus_ack_ic_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_dmmu_i,
  input                                 spr_bus_ack_dmmu_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_immu_i,
  input                                 spr_bus_ack_immu_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_mac_i,
  input                                 spr_bus_ack_mac_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_pmu_i,
  input                                 spr_bus_ack_pmu_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_pcu_i,
  input                                 spr_bus_ack_pcu_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_fpu_i,
  input                                 spr_bus_ack_fpu_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_tt_i,
  input                                 spr_bus_ack_tt_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_pic_i,
  input                                 spr_bus_ack_pic_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_gpr_i,
  input                                 spr_bus_ack_gpr_i,

  // WB: External Interrupt Collection
  output                                tt_interrupt_enable_o,
  output                                pic_interrupt_enable_o,
  input                                 wb_tt_interrupt_i,
  input                                 wb_pic_interrupt_i,

  // WB: programm counter
  input      [OPTION_OPERAND_WIDTH-1:0] pc_wb_i,

  // WB: flag
  input                                 wb_int_flag_set_i,
  input                                 wb_int_flag_clear_i,
  input                                 wb_fp32_flag_set_i,
  input                                 wb_fp32_flag_clear_i,
  input                                 wb_fp64_flag_set_i,
  input                                 wb_fp64_flag_clear_i,
  input                                 wb_atomic_flag_set_i,
  input                                 wb_atomic_flag_clear_i,
  input                                 wb_flag_wb_i,

  // WB: carry
  input                                 wb_div_carry_set_i,
  input                                 wb_div_carry_clear_i,
  input                                 wb_1clk_carry_set_i,
  input                                 wb_1clk_carry_clear_i,
  input                                 wb_carry_wb_i,

  // WB: overflow
  input                                 wb_div_overflow_set_i,
  input                                 wb_div_overflow_clear_i,
  input                                 wb_1clk_overflow_set_i,
  input                                 wb_1clk_overflow_clear_i,

  //  # FPX32 related flags
  //    ## comparison part
  input                                 wb_fp32_cmp_inv_i,
  input                                 wb_fp32_cmp_inf_i,
  input                                 wb_fp32_cmp_wb_fpcsr_i,
  input                                 wb_except_fp32_cmp_i,

  //  # FPX3264 arithmetic part
  input     [`OR1K_FPCSR_ALLF_SIZE-1:0] wb_fpxx_arith_fpcsr_i,
  input                                 wb_fpxx_arith_wb_fpcsr_i,
  input                                 wb_except_fpxx_arith_i,
  //  # FPX64 comparison part
  input                                 wb_fp64_cmp_inv_i,
  input                                 wb_fp64_cmp_inf_i,
  input                                 wb_fp64_cmp_wb_fpcsr_i,
  input                                 wb_except_fp64_cmp_i,

  //  # Excepion processing auxiliaries
  //    ## Exception PC input coming from the store buffer
  input      [OPTION_OPERAND_WIDTH-1:0] sbuf_eear_i,
  input      [OPTION_OPERAND_WIDTH-1:0] sbuf_epcr_i,
  input                                 sbuf_err_i,
  //    ## Instriction is in delay slot
  input                                 wb_delay_slot_i,

  //  # combined exceptions/interrupt flag
  input                                 exec_an_except_i, // to generate registered pipeline-flush
  input                                 wb_an_except_i,

  //  # particular IFETCH exception flags
  input                                 wb_except_ibus_err_i,
  input                                 wb_except_itlb_miss_i,
  input                                 wb_except_ipagefault_i,
  input                                 wb_except_ibus_align_i,

  //  # particular DECODE exception flags
  input                                 wb_except_illegal_i,
  input                                 wb_except_syscall_i,
  input                                 wb_except_trap_i,

  //  # particular LSU exception flags
  input                                 wb_except_dbus_err_i,
  input                                 wb_except_dtlb_miss_i,
  input                                 wb_except_dpagefault_i,
  input                                 wb_except_dbus_align_i,
  input      [OPTION_OPERAND_WIDTH-1:0] wb_lsu_except_addr_i,
  //  # LSU valid is miss (block padv-wb)
  input                                 wb_lsu_valid_miss_i,

  //  # overflow exception processing
  output                                except_overflow_enable_o,
  input                                 wb_except_overflow_div_i,
  input                                 wb_except_overflow_1clk_i,

  //  # Branch to exception/rfe processing address
  output                                ctrl_branch_exception_o,
  output     [OPTION_OPERAND_WIDTH-1:0] ctrl_branch_except_pc_o,
  input                                 fetch_exception_taken_i,
  //  # l.rfe
  input                                 exec_op_rfe_i, // to generate registered pipeline-flush
  input                                 wb_op_rfe_i,

  // Multicore related
  input      [OPTION_OPERAND_WIDTH-1:0] multicore_coreid_i,
  input      [OPTION_OPERAND_WIDTH-1:0] multicore_numcores_i,

  // Flag & Carry
  output                                ctrl_flag_o,
  output                                ctrl_carry_o,

  // Enable modules
  output                                ic_enable_o,
  output                                immu_enable_o,
  output                                dc_enable_o,
  output                                dmmu_enable_o,
  output                                supervisor_mode_o,

  // FPU related controls
  output                                except_fpu_enable_o,
  output    [`OR1K_FPCSR_ALLF_SIZE-1:0] ctrl_fpu_mask_flags_o,
  output      [`OR1K_FPCSR_RM_SIZE-1:0] ctrl_fpu_round_mode_o
);

  // Internal signals
  reg [SPR_SR_WIDTH-1:0]            spr_sr;
  reg [SPR_SR_WIDTH-1:0]            spr_esr;
  reg [OPTION_OPERAND_WIDTH-1:0]    spr_epcr;
  reg [OPTION_OPERAND_WIDTH-1:0]    spr_eear;


  // Exception vector base address
  localparam  SPR_EVBAR_LSB   = 13;
  localparam  SPR_EVBAR_WIDTH = OPTION_OPERAND_WIDTH - SPR_EVBAR_LSB;
  // ---
  reg  [SPR_EVBAR_WIDTH-1:0]        spr_evbar;
  wire [OPTION_OPERAND_WIDTH-1:0]   exception_pc_addr;


  // FPU Control & Status Register
  // and related exeption signals
  reg [`OR1K_FPCSR_WIDTH-1:0]       spr_fpcsr;

  reg [OPTION_OPERAND_WIDTH-1:0]    spr_ppc;
  reg [OPTION_OPERAND_WIDTH-1:0]    spr_npc;



  /* DU internal control signals */
  // SPR BUS acceess to DU's control registers
  wire                              spr_bus_cs_du;  // "chip select" for DU
  reg                               spr_bus_ack_du_r;
  wire                       [31:0] spr_bus_dat_du;
  // Access to NextPC SPR from Debug System through SPR BUS
  wire                              du_npc_we;
  wire                              du_npc_hold; // till restart command from Debug System
  // stall / unstall
  wire                              du_cpu_flush;
  wire                              du_cpu_stall;
  wire                              du_cpu_unstall;
  // step-by-step execution
  wire                              stepping;
  wire                        [3:0] pstep;
  wire                              stepped_into_delay_slot;
  wire                              stepped_into_exception;
  wire                              stepped_into_rfe;


  /* For SPR BUS transactions */
  reg                               spr_bus_wait_r;  // wait SPR ACK regardless on access validity
  reg                               spr_bus_mXspr_r; // access by l.mf(t)spr command indicator (for write back push)
  wire                              spr_bus_mXdbg;   // "move to/from Debug System"
  //  # instant ACK and data
  wire                              spr_bus_ack;
  wire   [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_mux;
  //  # registered ACK and data
  reg                               spr_bus_ack_r;
  reg    [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_r;
  //  # access to SYSTEM GROUP control registers
  //  # excluding GPR0
  wire                              spr_sys_group_cs;
  reg                               spr_sys_group_wr_r;
  reg                               spr_bus_ack_sys_group;
  reg                        [31:0] spr_bus_dat_sys_group;

  /* Wires from mor1kx_cfgrs module */
  wire [31:0]                       spr_vr;
  wire [31:0]                       spr_vr2;
  wire [31:0]                       spr_avr;
  wire [31:0]                       spr_upr;
  wire [31:0]                       spr_cpucfgr;
  wire [31:0]                       spr_dmmucfgr;
  wire [31:0]                       spr_immucfgr;
  wire [31:0]                       spr_dccfgr;
  wire [31:0]                       spr_iccfgr;
  wire [31:0]                       spr_dcfgr;
  wire [31:0]                       spr_pccfgr;
  //wire [31:0]                       spr_isr [0:7];


  // Flag output
  wire   ctrl_flag_clear = wb_int_flag_clear_i | wb_fp32_flag_clear_i | wb_fp64_flag_clear_i | wb_atomic_flag_clear_i;
  wire   ctrl_flag_set   = wb_int_flag_set_i   | wb_fp32_flag_set_i   | wb_fp64_flag_set_i   | wb_atomic_flag_set_i;
  // ---
  assign ctrl_flag_o     = (~ctrl_flag_clear) & (ctrl_flag_set | spr_sr[`OR1K_SPR_SR_F]);


  // Carry output
  wire   ctrl_carry_clear = wb_div_carry_clear_i | wb_1clk_carry_clear_i;
  wire   ctrl_carry_set   = wb_div_carry_set_i   | wb_1clk_carry_set_i;
  // ---
  assign ctrl_carry_o = (~ctrl_carry_clear) & (ctrl_carry_set | spr_sr[`OR1K_SPR_SR_CY]);


  // Overflow flag
  wire ctrl_overflow_clear = wb_div_overflow_clear_i | wb_1clk_overflow_clear_i;
  wire ctrl_overflow_set   = wb_div_overflow_set_i   | wb_1clk_overflow_set_i;
  // ---
  wire ctrl_overflow = (~ctrl_overflow_clear) & (ctrl_overflow_set | spr_sr[`OR1K_SPR_SR_OV]);


  // Overflow flag cause exception
  assign except_overflow_enable_o = spr_sr[`OR1K_SPR_SR_OVE];


  //-------------------------------------//
  // Exceptions processing support logic //
  //-------------------------------------//

  // PC next to WB
  wire [OPTION_OPERAND_WIDTH-1:0] pc_nxt_wb = pc_wb_i + 3'd4;

  // Exception PC

  //   ## Store address of latest jump/branch instruction
  //      (a) exception / interrupt in delay slot hadling
  //      (b) IBUS error handling
  reg [OPTION_OPERAND_WIDTH-1:0] last_jump_or_branch_pc;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      last_jump_or_branch_pc <= {OPTION_OPERAND_WIDTH{1'b0}};
    else if (pipeline_flush_o)
      last_jump_or_branch_pc <= {OPTION_OPERAND_WIDTH{1'b0}};
    else if (wb_jump_or_branch_i)
      last_jump_or_branch_pc <= pc_wb_i;
  end // @clock

  // default EPCR (for most exception cases)
  wire [OPTION_OPERAND_WIDTH-1:0] epcr_default = wb_delay_slot_i ? last_jump_or_branch_pc : pc_wb_i;
  
  // E-P-C-R update (hierarchy is same to exception vector)
  //   (a) On Syscall we return back to the instruction _after_
  //       the syscall instruction, unless the syscall was in a delay slot
  //   (b) We don't update EPCR on software breakpoint
  // ---
  always @(posedge clk`OR_ASYNC_RST) begin
    if (rst)
      spr_epcr <= {OPTION_OPERAND_WIDTH{1'b0}};
    else if (wb_an_except_i) begin
      // synthesis parallel_case full_case
      casez({(wb_except_itlb_miss_i | wb_except_ipagefault_i),
              wb_except_ibus_err_i,
             (wb_except_illegal_i   | wb_except_dbus_align_i | wb_except_ibus_align_i),
              wb_except_syscall_i,
             (wb_except_dtlb_miss_i | wb_except_dpagefault_i),
              wb_except_trap_i,
              sbuf_err_i
            })
        7'b1??????: spr_epcr <= epcr_default;                                           // ITLB miss, IPAGE fault
        7'b01?????: spr_epcr <= wb_jump_or_branch_i ? pc_wb_i : last_jump_or_branch_pc; // IBUS error
        7'b001????: spr_epcr <= epcr_default;                                           // Illegal, DBUS align, IBUS align
        7'b0001???: spr_epcr <= wb_delay_slot_i ? last_jump_or_branch_pc : pc_nxt_wb;   // syscall
        7'b00001??: spr_epcr <= epcr_default;                                           // DTLB miss, DPAGE fault
        7'b000001?: spr_epcr <= spr_epcr;                                               // software breakpoint
        7'b0000001: spr_epcr <= sbuf_epcr_i;                                            // Store buffer error
        default   : spr_epcr <= epcr_default;                                           // by default
      endcase
    end
    else if (spr_sys_group_cs & (`SPR_OFFSET(spr_bus_addr_o) == `SPR_OFFSET(`OR1K_SPR_EPCR0_ADDR)) &
             spr_sys_group_wr_r) begin
      spr_epcr <= spr_bus_dat_o;
    end
  end // @ clock

  // Store exception vector
  reg [4:0] exception_vector_r;
  //---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      exception_vector_r <= 5'd0;
    else if (wb_an_except_i) begin
      // synthesis parallel_case full_case
      casez({wb_except_itlb_miss_i,
             wb_except_ipagefault_i,
             wb_except_ibus_err_i,
             wb_except_illegal_i,
             (wb_except_dbus_align_i | wb_except_ibus_align_i),
             wb_except_syscall_i,
             wb_except_dtlb_miss_i,
             wb_except_dpagefault_i,
             wb_except_trap_i,
             (wb_except_dbus_err_i | sbuf_err_i),
             (wb_except_overflow_div_i | wb_except_overflow_1clk_i),
             (wb_except_fp32_cmp_i | wb_except_fp64_cmp_i | wb_except_fpxx_arith_i),
             wb_pic_interrupt_i,
             wb_tt_interrupt_i
            })
        14'b1?????????????: exception_vector_r <= `OR1K_ITLB_VECTOR;
        14'b01????????????: exception_vector_r <= `OR1K_IPF_VECTOR;
        14'b001???????????: exception_vector_r <= `OR1K_BERR_VECTOR;
        14'b0001??????????: exception_vector_r <= `OR1K_ILLEGAL_VECTOR;
        14'b00001?????????: exception_vector_r <= `OR1K_ALIGN_VECTOR;
        14'b000001????????: exception_vector_r <= `OR1K_SYSCALL_VECTOR;
        14'b0000001???????: exception_vector_r <= `OR1K_DTLB_VECTOR;
        14'b00000001??????: exception_vector_r <= `OR1K_DPF_VECTOR;
        14'b000000001?????: exception_vector_r <= `OR1K_TRAP_VECTOR;
        14'b0000000001????: exception_vector_r <= `OR1K_BERR_VECTOR;
        14'b00000000001???: exception_vector_r <= `OR1K_RANGE_VECTOR;
        14'b000000000001??: exception_vector_r <= `OR1K_FP_VECTOR;
        14'b0000000000001?: exception_vector_r <= `OR1K_INT_VECTOR;
        14'b00000000000001: exception_vector_r <= `OR1K_TT_VECTOR;
        default:            exception_vector_r <= `OR1K_RESET_VECTOR;
      endcase // casex (...
    end
  end // @ clock
  //---
  assign exception_pc_addr = {spr_evbar,exception_vector_r,8'd0};

  // flag to select l.rfe related branch vector
  reg doing_rfe_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      doing_rfe_r <= 1'b0;
    else if ((doing_rfe_r | du_cpu_unstall) & fetch_exception_taken_i)
      doing_rfe_r <= 1'b0;
    else if (wb_op_rfe_i)
      doing_rfe_r <= 1'b1;
  end // @ clock

  // flag to select exception related branch vector
  reg doing_exception_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      doing_exception_r <= 1'b0;
    else if ((doing_exception_r | du_cpu_unstall) & fetch_exception_taken_i)
      doing_exception_r <= 1'b0;
    else if (wb_an_except_i)
      doing_exception_r <= 1'b1;
  end // @ clock

  // To FETCH:
  //   Flag to use DU/exceptions/rfe provided address
  assign ctrl_branch_exception_o = du_cpu_unstall | doing_exception_r | doing_rfe_r;
  //   DU/exceptions/rfe provided address itself
  assign ctrl_branch_except_pc_o = du_cpu_unstall    ? spr_npc           :
                                   doing_exception_r ? exception_pc_addr :
                                                       spr_epcr;


  //--------------------------------//
  // special flag that WB is active //
  //--------------------------------//

  // 1-clock length 1-clock delayed padv-wb-o for updating SPRs
  reg  ctrl_spr_wb_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      ctrl_spr_wb_r <= 1'b0;
    else if (pipeline_flush_o)
      ctrl_spr_wb_r <= 1'b0;
    else if (padv_wb_o)
      ctrl_spr_wb_r <= 1'b1;
    else
      ctrl_spr_wb_r <= 1'b0;
  end // @ clock


  //------------------------//
  // Pipeline control logic //
  //------------------------//

  // Pipeline flush by DU/exceptions/rfe (l.rfe is in wb-an-except)
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      pipeline_flush_o <= 1'b0;
    else if (pipeline_flush_o)
      pipeline_flush_o <= 1'b0;
    else if (padv_wb_o | du_cpu_flush)
      pipeline_flush_o <= (exec_an_except_i | exec_op_rfe_i | du_cpu_flush);
  end // @ clock


  // Advance IFETCH
  assign padv_fetch_o = (dcod_valid_i | (~dcod_insn_valid_i)) & (~spr_bus_wait_r) & (~fetch_an_except_i) & (~oman_fd_an_except_i) &
                        (~du_cpu_stall) & ((~stepping) | pstep[0]); // DU enabling/disabling IFETCH
  // Pass step from IFETCH to DECODE
  wire   pass_step_to_decode = dcod_insn_valid_i & pstep[0]; // for DU


  // Advance DECODE->EXECUTE latches
  assign padv_decode_o = dcod_valid_i & dcod_insn_valid_i & (~spr_bus_wait_r) & (~oman_fd_an_except_i) &
                         (~du_cpu_stall) & ((~stepping) | pstep[1]); // DU enabling/disabling DECODE
  // Pass step from DECODE to WB
  wire   pass_step_to_wb = pstep[1]; // for DU


  // Advance Write Back latches
  assign padv_wb_o = ((exec_valid_i & (~spr_bus_wait_r) & (~wb_lsu_valid_miss_i)) | (spr_bus_ack_r & spr_bus_mXspr_r)) &
                     (~du_cpu_stall) & ((~stepping) | pstep[2]); // DU enabling/disabling WRITE-BACK
  // Complete the step
  wire   pass_step_to_stall = (exec_valid_i | (spr_bus_ack_r & spr_bus_mXspr_r)) & pstep[2]; // for DU


  //-----------------------------------//
  // FPU related: FPCSR and exceptions //
  //-----------------------------------//

  assign except_fpu_enable_o = spr_fpcsr[`OR1K_FPCSR_FPEE];

  wire spr_fpcsr_we = spr_sys_group_cs &
                      (`SPR_OFFSET(spr_bus_addr_o) == `SPR_OFFSET(`OR1K_SPR_FPCSR_ADDR)) &
                      spr_sys_group_wr_r &  spr_sr[`OR1K_SPR_SR_SM];

 `ifdef OR1K_FPCSR_MASK_FLAGS
  reg [`OR1K_FPCSR_ALLF_SIZE-1:0] ctrl_fpu_mask_flags_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      ctrl_fpu_mask_flags_r <= {`OR1K_FPCSR_ALLF_SIZE{1'b1}};
    else if (spr_fpcsr_we)
      ctrl_fpu_mask_flags_r <= spr_bus_dat_o[`OR1K_FPCSR_MASK_ALL];
  end
  // ---
  assign ctrl_fpu_mask_flags_o = ctrl_fpu_mask_flags_r;         // FPU-enabled, "masking FPU flags" enabled
 `else
  assign ctrl_fpu_mask_flags_o = {`OR1K_FPCSR_ALLF_SIZE{1'b1}}; // FPU-enabled, "masking FPU flags" disabled
 `endif

  assign ctrl_fpu_round_mode_o = spr_fpcsr[`OR1K_FPCSR_RM];

  // collect FPx flags
  wire [`OR1K_FPCSR_ALLF_SIZE-1:0] fpx_flags = {1'b0, wb_fp32_cmp_inf_i, wb_fp32_cmp_inv_i, 6'd0} |
                                               {1'b0, wb_fp64_cmp_inf_i, wb_fp64_cmp_inv_i, 6'd0} |
                                               wb_fpxx_arith_fpcsr_i;

  // FPU Control & Status Register
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      spr_fpcsr <= `OR1K_FPCSR_RESET_VALUE;
    else if (spr_fpcsr_we)
      spr_fpcsr <= spr_bus_dat_o[`OR1K_FPCSR_WIDTH-1:0]; // update all fields
    else if (wb_fp32_cmp_wb_fpcsr_i | wb_fp64_cmp_wb_fpcsr_i | wb_fpxx_arith_wb_fpcsr_i)
      spr_fpcsr <= {fpx_flags, spr_fpcsr[`OR1K_FPCSR_RM], spr_fpcsr[`OR1K_FPCSR_FPEE]};
  end


  //----------------------//
  // Supervision register //
  //----------------------//

  // WB: External Interrupt Collection
  assign  tt_interrupt_enable_o  = spr_sr[`OR1K_SPR_SR_TEE];
  assign  pic_interrupt_enable_o = spr_sr[`OR1K_SPR_SR_IEE];
  // enable modules
  assign  ic_enable_o       = spr_sr[`OR1K_SPR_SR_ICE];
  assign  immu_enable_o     = spr_sr[`OR1K_SPR_SR_IME];
  assign  dc_enable_o       = spr_sr[`OR1K_SPR_SR_DCE];
  assign  dmmu_enable_o     = spr_sr[`OR1K_SPR_SR_DME];
  assign  supervisor_mode_o = spr_sr[`OR1K_SPR_SR_SM];
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      spr_sr <= SPR_SR_RESET_VALUE;
    else if (wb_an_except_i) begin
      // Go into supervisor mode, disable interrupts, MMUs
      // it doesn't matter if the next features are enabled or not
      spr_sr[`OR1K_SPR_SR_SM ] <= 1'b1; // supervisor mode
      spr_sr[`OR1K_SPR_SR_TEE] <= 1'b0; // block interrupt from timer
      spr_sr[`OR1K_SPR_SR_IEE] <= 1'b0; // block interrupt from PIC
      spr_sr[`OR1K_SPR_SR_DME] <= 1'b0; // D-MMU is off
      spr_sr[`OR1K_SPR_SR_IME] <= 1'b0; // I-MMU is off
      spr_sr[`OR1K_SPR_SR_OVE] <= 1'b0; // block overflow excep.
      spr_sr[`OR1K_SPR_SR_OV ] <= wb_except_overflow_div_i | wb_except_overflow_1clk_i;
      spr_sr[`OR1K_SPR_SR_DSX] <= wb_delay_slot_i;
    end
    else if (spr_sys_group_cs & (`SPR_OFFSET(spr_bus_addr_o) == `SPR_OFFSET(`OR1K_SPR_SR_ADDR)) &
             spr_sys_group_wr_r &
             spr_sr[`OR1K_SPR_SR_SM]) begin
      // from SPR bus
      spr_sr[`OR1K_SPR_SR_SM ] <= spr_bus_dat_o[`OR1K_SPR_SR_SM ];
      spr_sr[`OR1K_SPR_SR_F  ] <= spr_bus_dat_o[`OR1K_SPR_SR_F  ];
      spr_sr[`OR1K_SPR_SR_TEE] <= spr_bus_dat_o[`OR1K_SPR_SR_TEE];
      spr_sr[`OR1K_SPR_SR_IEE] <= spr_bus_dat_o[`OR1K_SPR_SR_IEE];
      spr_sr[`OR1K_SPR_SR_DCE] <= spr_bus_dat_o[`OR1K_SPR_SR_DCE];
      spr_sr[`OR1K_SPR_SR_ICE] <= spr_bus_dat_o[`OR1K_SPR_SR_ICE];
      spr_sr[`OR1K_SPR_SR_DME] <= spr_bus_dat_o[`OR1K_SPR_SR_DME];
      spr_sr[`OR1K_SPR_SR_IME] <= spr_bus_dat_o[`OR1K_SPR_SR_IME];
      spr_sr[`OR1K_SPR_SR_CE ] <= 1'b0;
      spr_sr[`OR1K_SPR_SR_CY ] <= spr_bus_dat_o[`OR1K_SPR_SR_CY ];
      spr_sr[`OR1K_SPR_SR_OV ] <= spr_bus_dat_o[`OR1K_SPR_SR_OV ];
      spr_sr[`OR1K_SPR_SR_OVE] <= spr_bus_dat_o[`OR1K_SPR_SR_OVE];
      spr_sr[`OR1K_SPR_SR_DSX] <= spr_bus_dat_o[`OR1K_SPR_SR_DSX];
      spr_sr[`OR1K_SPR_SR_EPH] <= spr_bus_dat_o[`OR1K_SPR_SR_EPH];
    end
    else if (wb_op_rfe_i) begin
      // Skip FO. TODO: make this even more selective.
      spr_sr[14:0] <= spr_esr[14:0];
    end
    else begin
      // OVERFLOW field update
      if (ctrl_spr_wb_r)                           // OVERFLOW field update
        spr_sr[`OR1K_SPR_SR_OV] <= ctrl_overflow;
      // FLAG field update (taking into accaunt specualtive WB for LSU)
      if (wb_flag_wb_i)                            // FLAG field update
        spr_sr[`OR1K_SPR_SR_F]  <= ctrl_flag_o;
      // CARRY field update
      if (wb_carry_wb_i)                           // CARRY field update
        spr_sr[`OR1K_SPR_SR_CY] <= ctrl_carry_o;
    end
  end // @ clock

  // Exception SR
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      spr_esr <= SPR_SR_RESET_VALUE;
    else if (wb_an_except_i)
      spr_esr <= spr_sr; // by exceptions
    else if (spr_sys_group_cs & (`SPR_OFFSET(spr_bus_addr_o) == `SPR_OFFSET(`OR1K_SPR_ESR0_ADDR)) &
             spr_sys_group_wr_r)
      spr_esr <= spr_bus_dat_o[SPR_SR_WIDTH-1:0];
  end // @ clock


  // Exception Effective Address
  wire lsu_err = wb_except_dbus_align_i | wb_except_dtlb_miss_i | wb_except_dpagefault_i;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      spr_eear <= {OPTION_OPERAND_WIDTH{1'b0}};
    else if (wb_an_except_i) begin
      spr_eear <= lsu_err    ? wb_lsu_except_addr_i :
                  sbuf_err_i ? sbuf_eear_i          :
                               pc_wb_i;
    end
  end // @ clock


  // Track PC
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      spr_ppc <= OPTION_RESET_PC;
    else if (ctrl_spr_wb_r) // Track PC
      spr_ppc <= pc_wb_i;
  end // @ clock


  // Target of last taken branch.
  // To set correct NPC at delay slot in WB
  reg [OPTION_OPERAND_WIDTH-1:0] pc_next_to_delay_slot;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      pc_next_to_delay_slot <= {OPTION_OPERAND_WIDTH{1'b0}};
    // !!! don't flush it because it is used for stepped_into_delay_slot !!!
    else if (wb_jump_or_branch_i)
      pc_next_to_delay_slot <= wb_do_branch_i ? wb_do_branch_target_i : (pc_wb_i + 4'd8);
  end // @ clock


  // NPC for SPR (write accesses implemented for Debug System only)
  assign du_npc_we = (spr_sys_group_cs & (`SPR_OFFSET(spr_bus_addr_o) == `SPR_OFFSET(`OR1K_SPR_NPC_ADDR)) &
                      spr_sys_group_wr_r & spr_bus_mXdbg);
  // --- Actually it is used just to restart CPU after salling by DU ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      spr_npc <= OPTION_RESET_PC;
    else if (du_npc_we)          // Write restart PC and ...
      spr_npc <= du_dat_i;
    else if (~du_npc_hold) begin // ... hold it till restart command from Debug System
      if (ctrl_spr_wb_r) begin                                // Track NPC: regular update
        spr_npc <= wb_except_trap_i ? pc_wb_i               : // Track NPC: regular update
                   wb_delay_slot_i  ? pc_next_to_delay_slot : // Track NPC: regular update
                                      pc_nxt_wb;              // Track NPC: regular update
      end
      else begin
        // any "stepped_into_*" is 1-clock delayed "ctrl_spr_wb_r"
        spr_npc <= stepped_into_exception  ? exception_pc_addr     : // Track NPC: step-by-step
                   stepped_into_rfe        ? spr_epcr              : // Track NPC: step-by-step
                   stepped_into_delay_slot ? pc_next_to_delay_slot : // Track NPC: step-by-step
                                             spr_npc;                // Track NPC: step-by-step
      end
    end
  end // @ clock

  // Exception Vector Address
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      spr_evbar <= {SPR_EVBAR_WIDTH{1'b0}};
    else if (spr_sys_group_cs & (`SPR_OFFSET(spr_bus_addr_o) == `SPR_OFFSET(`OR1K_SPR_EVBAR_ADDR)) &
             spr_sys_group_wr_r)
      spr_evbar <= spr_bus_dat_o[(OPTION_OPERAND_WIDTH-1):SPR_EVBAR_LSB];
  end // @ clock

  // configuration registers
  mor1kx_cfgrs
  #(
    .FEATURE_PIC                     ("ENABLED"), // mor1kx_cfgrs instance: marocchino
    .FEATURE_TIMER                   ("ENABLED"), // mor1kx_cfgrs instance: marocchino
    .OPTION_PIC_TRIGGER              (OPTION_PIC_TRIGGER),
    .FEATURE_DSX                     ("ENABLED"), // mor1kx_cfgrs instance: marocchino
    .FEATURE_FASTCONTEXTS            ("NONE"), // mor1kx_cfgrs instance: marocchino
    .OPTION_RF_NUM_SHADOW_GPR        (0), // mor1kx_cfgrs instance: marocchino
    .FEATURE_OVERFLOW                ("ENABLED"), // mor1kx_cfgrs instance: marocchino
    .FEATURE_DATACACHE               ("ENABLED"), // mor1kx_cfgrs instance: marocchino
    .OPTION_DCACHE_BLOCK_WIDTH       (OPTION_DCACHE_BLOCK_WIDTH), // mor1kx_cfgrs instance:
    .OPTION_DCACHE_SET_WIDTH         (OPTION_DCACHE_SET_WIDTH), // mor1kx_cfgrs instance:
    .OPTION_DCACHE_WAYS              (OPTION_DCACHE_WAYS), // mor1kx_cfgrs instance:
    .FEATURE_DMMU                    ("ENABLED"), // mor1kx_cfgrs instance: marocchino
    .OPTION_DMMU_SET_WIDTH           (OPTION_DMMU_SET_WIDTH), // mor1kx_cfgrs instance:
    .OPTION_DMMU_WAYS                (OPTION_DMMU_WAYS), // mor1kx_cfgrs instance:
    .FEATURE_INSTRUCTIONCACHE        ("ENABLED"), // mor1kx_cfgrs instance: marocchino
    .OPTION_ICACHE_BLOCK_WIDTH       (OPTION_ICACHE_BLOCK_WIDTH), // mor1kx_cfgrs instance:
    .OPTION_ICACHE_SET_WIDTH         (OPTION_ICACHE_SET_WIDTH), // mor1kx_cfgrs instance:
    .OPTION_ICACHE_WAYS              (OPTION_ICACHE_WAYS), // mor1kx_cfgrs instance:
    .FEATURE_IMMU                    ("ENABLED"), // mor1kx_cfgrs instance: marocchino
    .OPTION_IMMU_SET_WIDTH           (OPTION_IMMU_SET_WIDTH), // mor1kx_cfgrs instance:
    .OPTION_IMMU_WAYS                (OPTION_IMMU_WAYS), // mor1kx_cfgrs instance:
    .FEATURE_DEBUGUNIT               (FEATURE_DEBUGUNIT), // mor1kx_cfgrs instance:
    .FEATURE_PERFCOUNTERS            (FEATURE_PERFCOUNTERS), // mor1kx_cfgrs instance:
    .FEATURE_MAC                     (FEATURE_MAC), // mor1kx_cfgrs instance:
    .FEATURE_FPU                     ("ENABLED"), // mor1kx_cfgrs instance: marocchino
    .FEATURE_FPU64                   ("ENABLED"), // mor1kx_cfgrs instance: marocchino
    .FEATURE_SYSCALL                 ("ENABLED"), // mor1kx_cfgrs instance: marocchino
    .FEATURE_TRAP                    ("ENABLED"), // mor1kx_cfgrs instance: marocchino
    .FEATURE_RANGE                   ("ENABLED"), // mor1kx_cfgrs instance: marocchino
    .FEATURE_DELAYSLOT               ("ENABLED"), // mor1kx_cfgrs instance: marocchino
    .FEATURE_EVBAR                   ("ENABLED") // mor1kx_cfgrs instance: marocchino
  )
  u_cfgrs
  (
    // Outputs
    .spr_vr                           (spr_vr[31:0]),
    .spr_vr2                          (spr_vr2[31:0]),
    .spr_upr                          (spr_upr[31:0]),
    .spr_cpucfgr                      (spr_cpucfgr[31:0]),
    .spr_dmmucfgr                     (spr_dmmucfgr[31:0]),
    .spr_immucfgr                     (spr_immucfgr[31:0]),
    .spr_dccfgr                       (spr_dccfgr[31:0]),
    .spr_iccfgr                       (spr_iccfgr[31:0]),
    .spr_dcfgr                        (spr_dcfgr[31:0]),
    .spr_pccfgr                       (spr_pccfgr[31:0]),
    .spr_avr                          (spr_avr[31:0])
  );

  // Implementation-specific registers
  /*
  assign spr_isr[0] = 32'd0;
  assign spr_isr[1] = 32'd0;
  assign spr_isr[2] = 32'd0;
  assign spr_isr[3] = 32'd0;
  assign spr_isr[4] = 32'd0;
  assign spr_isr[5] = 32'd0;
  assign spr_isr[6] = 32'd0;
  assign spr_isr[7] = 32'd0;
  */


  //---------------------------------------------------------------------------//
  // SPR access control                                                        //
  //   Allow accesses from either the instructions or from the debug interface //
  //---------------------------------------------------------------------------//

  // Accees to SPR BUS from l.mf(t)spr command or debug unit
  wire take_op_mXspr = padv_decode_o & (dcod_op_mfspr_i | dcod_op_mtspr_i);

  // Access to SPR BUS from Debug System
  wire take_access_du = (~take_op_mXspr) & (~spr_bus_wait_r) & du_stb_i;

  // SPR address for latch
  wire [15:0] spr_addr_mux = take_op_mXspr ? (dcod_rfa1_i[15:0] | dcod_imm16_i) :
                                              du_addr_i;

  // Is accessiblr SPR is present
  reg spr_access_valid_mux;
  reg spr_access_valid_reg; // SPR ACK in case of access to not existing modules
  //---
  always @(*) begin
    // synthesis parallel_case full_case
    case(`SPR_BASE(spr_addr_mux))
      // system registers
      `OR1K_SPR_SYS_BASE:  spr_access_valid_mux = 1'b1;
      // modules registers
      `OR1K_SPR_DMMU_BASE: spr_access_valid_mux = 1'b1;
      `OR1K_SPR_IMMU_BASE: spr_access_valid_mux = 1'b1;
      `OR1K_SPR_DC_BASE:   spr_access_valid_mux = 1'b1;
      `OR1K_SPR_IC_BASE:   spr_access_valid_mux = 1'b1;
      `OR1K_SPR_MAC_BASE:  spr_access_valid_mux = (FEATURE_MAC          != "NONE");
      `OR1K_SPR_DU_BASE:   spr_access_valid_mux = (FEATURE_DEBUGUNIT    != "NONE");
      `OR1K_SPR_PC_BASE:   spr_access_valid_mux = (FEATURE_PERFCOUNTERS != "NONE");
      `OR1K_SPR_PM_BASE:   spr_access_valid_mux = (FEATURE_PMU          != "NONE");
      `OR1K_SPR_PIC_BASE:  spr_access_valid_mux = 1'b1;
      `OR1K_SPR_TT_BASE:   spr_access_valid_mux = 1'b1;
      `OR1K_SPR_FPU_BASE:  spr_access_valid_mux = 1'b0; // actual FPU implementation havn't got control registers
      // invalid if the group is not present in the design
      default:             spr_access_valid_mux = 1'b0;
    endcase
  end // always

  //
  //   Before issuing MT(F)SPR, OMAN waits till order control buffer has become
  // empty. Also we don't issue new instruction till l.mf(t)spr completion.
  //   So, we don't need neither forwarding nor 'grant' signals here.
  //

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      spr_bus_addr_o  <= 16'd0; // on reset
      spr_bus_we_o    <=  1'b0; // on reset
      spr_bus_stb_o   <=  1'b0; // on reset
      spr_bus_dat_o   <= {OPTION_OPERAND_WIDTH{1'b0}}; // on reset
      // internal auxiliaries
      spr_bus_wait_r       <= 1'b0; // on reset
      spr_bus_mXspr_r      <= 1'b0; // on reset
      spr_access_valid_reg <= 1'b1; // on reset
      // Registered ACK and data
      spr_bus_ack_r   <=  1'b0; // on reset
      spr_bus_dat_r   <= {OPTION_OPERAND_WIDTH{1'b0}}; // on reset
    end
    else if (pipeline_flush_o) begin
      spr_bus_addr_o  <= 16'd0; // on reset
      spr_bus_we_o    <=  1'b0; // on reset
      spr_bus_stb_o   <=  1'b0; // on reset
      spr_bus_dat_o   <= {OPTION_OPERAND_WIDTH{1'b0}}; // on reset
      // internal auxiliaries
      spr_bus_wait_r       <= 1'b0; // on reset
      spr_bus_mXspr_r      <= 1'b0; // on reset
      spr_access_valid_reg <= 1'b1; // on reset
      // Registered ACK and data
      spr_bus_ack_r   <=  1'b0; // on reset
      spr_bus_dat_r   <= {OPTION_OPERAND_WIDTH{1'b0}}; // on reset
    end
    else if (spr_bus_ack_r) begin
      // internal auxiliaries
      spr_bus_wait_r       <= 1'b0; // on read completion with registering
      spr_bus_mXspr_r      <= 1'b0; // on read completion with registering
      spr_access_valid_reg <= 1'b1; // on read completion with registering
      // Registered ACK and data
      spr_bus_ack_r   <=  1'b0; // on read completion with registering
      spr_bus_dat_r   <= {OPTION_OPERAND_WIDTH{1'b0}}; // on read completion with registering
    end
    else if (spr_bus_ack) begin
      spr_bus_addr_o  <= 16'd0;
      spr_bus_we_o    <=  1'b0;
      spr_bus_stb_o   <=  1'b0;
      spr_bus_dat_o   <= {OPTION_OPERAND_WIDTH{1'b0}};
      // Registered ACK and data
      spr_bus_ack_r   <= 1'b1; // on read completion: registering
      spr_bus_dat_r   <= spr_bus_dat_mux; // on read completion: registering
    end
    else if (take_op_mXspr | take_access_du) begin
      if (spr_access_valid_mux) begin
        spr_bus_addr_o <= spr_addr_mux;
        spr_bus_we_o   <= take_op_mXspr ? dcod_op_mtspr_i : du_we_i;
        spr_bus_stb_o  <= 1'b1;
        spr_bus_dat_o  <= take_op_mXspr ? dcod_rfb1_i : du_dat_i;
      end
      // internal auxiliaries
      spr_bus_wait_r       <= 1'b1; // on access initialization
      spr_bus_mXspr_r      <= take_op_mXspr; // on access initialization
      spr_access_valid_reg <= spr_access_valid_mux; // on access initialization
    end
  end // @clock


  // System group (0) SPR data out
  reg [OPTION_OPERAND_WIDTH-1:0]    spr_sys_group_dat;
  // ---
  always @(*) begin
    // synthesis parallel_case full_case
    case(`SPR_OFFSET(spr_bus_addr_o))
      `SPR_OFFSET(`OR1K_SPR_VR_ADDR)      : spr_sys_group_dat = spr_vr;
      `SPR_OFFSET(`OR1K_SPR_UPR_ADDR)     : spr_sys_group_dat = spr_upr;
      `SPR_OFFSET(`OR1K_SPR_CPUCFGR_ADDR) : spr_sys_group_dat = spr_cpucfgr;
      `SPR_OFFSET(`OR1K_SPR_DMMUCFGR_ADDR): spr_sys_group_dat = spr_dmmucfgr;
      `SPR_OFFSET(`OR1K_SPR_IMMUCFGR_ADDR): spr_sys_group_dat = spr_immucfgr;
      `SPR_OFFSET(`OR1K_SPR_DCCFGR_ADDR)  : spr_sys_group_dat = spr_dccfgr;
      `SPR_OFFSET(`OR1K_SPR_ICCFGR_ADDR)  : spr_sys_group_dat = spr_iccfgr;
      `SPR_OFFSET(`OR1K_SPR_DCFGR_ADDR)   : spr_sys_group_dat = spr_dcfgr;
      `SPR_OFFSET(`OR1K_SPR_PCCFGR_ADDR)  : spr_sys_group_dat = spr_pccfgr;
      `SPR_OFFSET(`OR1K_SPR_VR2_ADDR)     : spr_sys_group_dat = {spr_vr2[31:8], `MOR1KX_PIPEID_CAPPUCCINO};
      `SPR_OFFSET(`OR1K_SPR_AVR_ADDR)     : spr_sys_group_dat = spr_avr;
      `SPR_OFFSET(`OR1K_SPR_EVBAR_ADDR)   : spr_sys_group_dat = {spr_evbar,{SPR_EVBAR_LSB{1'b0}}};
      `SPR_OFFSET(`OR1K_SPR_NPC_ADDR)     : spr_sys_group_dat = spr_npc;
      `SPR_OFFSET(`OR1K_SPR_SR_ADDR)      : spr_sys_group_dat = {{(OPTION_OPERAND_WIDTH-SPR_SR_WIDTH){1'b0}},
                                                                  spr_sr};
      `SPR_OFFSET(`OR1K_SPR_PPC_ADDR)     : spr_sys_group_dat = spr_ppc;
     `ifdef OR1K_FPCSR_MASK_FLAGS
      `SPR_OFFSET(`OR1K_SPR_FPCSR_ADDR)   : spr_sys_group_dat = {{(OPTION_OPERAND_WIDTH-`OR1K_FPCSR_WIDTH-`OR1K_FPCSR_ALLF_SIZE){1'b0}},
                                                                  ctrl_fpu_mask_flags_o,spr_fpcsr};
     `else
      `SPR_OFFSET(`OR1K_SPR_FPCSR_ADDR)   : spr_sys_group_dat = {{(OPTION_OPERAND_WIDTH-`OR1K_FPCSR_WIDTH){1'b0}},
                                                                  spr_fpcsr};
     `endif
      `SPR_OFFSET(`OR1K_SPR_ISR0_ADDR)    : spr_sys_group_dat = {OPTION_OPERAND_WIDTH{1'b0}}; // spr_isr[0];
      `SPR_OFFSET(`OR1K_SPR_ISR0_ADDR) +1 : spr_sys_group_dat = {OPTION_OPERAND_WIDTH{1'b0}}; // spr_isr[1];
      `SPR_OFFSET(`OR1K_SPR_ISR0_ADDR) +2 : spr_sys_group_dat = {OPTION_OPERAND_WIDTH{1'b0}}; // spr_isr[2];
      `SPR_OFFSET(`OR1K_SPR_ISR0_ADDR) +3 : spr_sys_group_dat = {OPTION_OPERAND_WIDTH{1'b0}}; // spr_isr[3];
      `SPR_OFFSET(`OR1K_SPR_ISR0_ADDR) +4 : spr_sys_group_dat = {OPTION_OPERAND_WIDTH{1'b0}}; // spr_isr[4];
      `SPR_OFFSET(`OR1K_SPR_ISR0_ADDR) +5 : spr_sys_group_dat = {OPTION_OPERAND_WIDTH{1'b0}}; // spr_isr[5];
      `SPR_OFFSET(`OR1K_SPR_ISR0_ADDR) +6 : spr_sys_group_dat = {OPTION_OPERAND_WIDTH{1'b0}}; // spr_isr[6];
      `SPR_OFFSET(`OR1K_SPR_ISR0_ADDR) +7 : spr_sys_group_dat = {OPTION_OPERAND_WIDTH{1'b0}}; // spr_isr[7];
      `SPR_OFFSET(`OR1K_SPR_EPCR0_ADDR)   : spr_sys_group_dat = spr_epcr;
      `SPR_OFFSET(`OR1K_SPR_EEAR0_ADDR)   : spr_sys_group_dat = spr_eear;
      `SPR_OFFSET(`OR1K_SPR_ESR0_ADDR)    : spr_sys_group_dat = {{(OPTION_OPERAND_WIDTH-SPR_SR_WIDTH){1'b0}},
                                                                  spr_esr};

      // If the multicore feature is activated this address returns the
      // core identifier, 0 otherwise
      `SPR_OFFSET(`OR1K_SPR_COREID_ADDR)  : spr_sys_group_dat = (FEATURE_MULTICORE != "NONE") ?
                                                                  multicore_coreid_i : 0;
      // If the multicore feature is activated this address returns the
      // core identifier, 0 otherwise
      `SPR_OFFSET(`OR1K_SPR_NUMCORES_ADDR): spr_sys_group_dat = (FEATURE_MULTICORE != "NONE") ?
                                                                  multicore_numcores_i : 0;

      default:                              spr_sys_group_dat = {OPTION_OPERAND_WIDTH{1'b0}};
    endcase
  end // always

  // SPR BUS interface for SYSTEM GROUP
  //  !!! Excluding GPR0 !!!
  assign spr_sys_group_cs = spr_bus_stb_o & (`SPR_BASE(spr_bus_addr_o) == `OR1K_SPR_SYS_BASE);
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      spr_sys_group_wr_r    <=  1'b0;
      spr_bus_ack_sys_group <=  1'b0;
      spr_bus_dat_sys_group <= 32'd0;
    end
    else if (spr_bus_ack_sys_group) begin // end of cycle
      spr_sys_group_wr_r    <=  1'b0;
      spr_bus_ack_sys_group <=  1'b0;
      spr_bus_dat_sys_group <= 32'd0;
    end
    else if (spr_sys_group_cs & (spr_bus_addr_o[15:10] != 6'b000001)) begin // and not acceess to GPR (see OR1K_SPR_GPR0_ADDR)
      if (spr_bus_we_o) begin
        spr_sys_group_wr_r    <=  1'b1;
        spr_bus_ack_sys_group <=  1'b1;
        spr_bus_dat_sys_group <= 32'd0;
      end
      else begin
        spr_sys_group_wr_r    <= 1'b0;
        spr_bus_ack_sys_group <= 1'b1;
        spr_bus_dat_sys_group <= spr_sys_group_dat;
      end
    end
  end // at clock


  // SPR access "ACK"
  assign spr_bus_ack = spr_bus_ack_sys_group | spr_bus_ack_gpr_i  |
                       spr_bus_ack_dmmu_i    | spr_bus_ack_immu_i |
                       spr_bus_ack_dc_i      | spr_bus_ack_ic_i   |
                       spr_bus_ack_mac_i     | spr_bus_ack_du_r   |
                       spr_bus_ack_pcu_i     | spr_bus_ack_pmu_i  |
                       spr_bus_ack_pic_i     | spr_bus_ack_tt_i   |
                       spr_bus_ack_fpu_i     | (~spr_access_valid_reg);

  //
  // Generate data to the register file for mfspr operations
  // Read datas are simply ORed since set to 0 when not
  // concerned by spr access.
  //
  assign spr_bus_dat_mux = spr_bus_dat_sys_group | spr_bus_dat_gpr_i  |
                           spr_bus_dat_dmmu_i    | spr_bus_dat_immu_i |
                           spr_bus_dat_dc_i      | spr_bus_dat_ic_i   |
                           spr_bus_dat_mac_i     | spr_bus_dat_du     |
                           spr_bus_dat_pcu_i     | spr_bus_dat_pmu_i  |
                           spr_bus_dat_pic_i     | spr_bus_dat_tt_i   |
                           spr_bus_dat_fpu_i;


  // MFSPR data and flag for WB_MUX
  always @(posedge clk) begin
    if (padv_wb_o)
      wb_mfspr_dat_o <= {OPTION_OPERAND_WIDTH{spr_bus_mXspr_r}} & spr_bus_dat_r;
  end // @clock



  //------------//
  // DEBUG unit //
  //------------//

  // "chip select" for DU from SPR BUS
  assign spr_bus_cs_du = spr_bus_stb_o & (`SPR_BASE(spr_bus_addr_o) == `OR1K_SPR_DU_BASE);

  generate

  /* verilator lint_off WIDTH */
  if (FEATURE_DEBUGUNIT != "NONE") begin : du_enabled
  /* verilator lint_on WIDTH */

    /* Generate answers to Debug System */

    // "move to/from Debbug System"
    reg spr_bus_mXdbg_r;
    // Generate ack back to the debug interface bus
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst) begin
        spr_bus_mXdbg_r <= 1'b0;
        du_ack_o        <= 1'b0;
      end
      else if (du_ack_o) begin
        spr_bus_mXdbg_r <= 1'b0;
        du_ack_o        <= 1'b0;
      end
      else if (spr_bus_mXdbg_r) begin
        if (spr_bus_ack) begin // DU uses non-registered SPR BUS sources
          spr_bus_mXdbg_r <= 1'b0;
          du_ack_o        <= 1'b1;
        end
      end
      else if (take_access_du) begin
        spr_bus_mXdbg_r <= 1'b1;
        du_ack_o        <= 1'b0;
      end
    end // @ clock
    // ---
    assign spr_bus_mXdbg = spr_bus_mXdbg_r;


    // Data back to the debug bus
    reg [OPTION_OPERAND_WIDTH-1:0] du_dat_r;
    // ---
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        du_dat_r <= {OPTION_OPERAND_WIDTH{1'b0}};
      else if (spr_bus_ack & spr_bus_mXdbg & (~spr_bus_we_o)) // DU uses non-registered SPR BUS sources
        du_dat_r <= spr_bus_dat_mux; // DU uses non-registered SPR BUS sources
    end
    // ---
    assign du_dat_o = du_dat_r; // DU enabled

    /* DU's Control registers and SPR BUS access cycle */

    reg spr_dmr1_st;
    reg spr_dsr_te;
    reg spr_drr_te;

    wire spr_bus_cs_du_dmr1 = (`SPR_OFFSET(spr_bus_addr_o) == `SPR_OFFSET(`OR1K_SPR_DMR1_ADDR));
    wire spr_bus_cs_du_dsr  = (`SPR_OFFSET(spr_bus_addr_o) == `SPR_OFFSET(`OR1K_SPR_DSR_ADDR));
    wire spr_bus_cs_du_drr  = (`SPR_OFFSET(spr_bus_addr_o) == `SPR_OFFSET(`OR1K_SPR_DRR_ADDR));

    reg spr_du_wr_r;
    reg spr_bus_du_dmr1_st_r, spr_bus_du_dXr_te_r;

    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst) begin
        spr_du_wr_r           <= 1'b0;
        spr_bus_ack_du_r      <= 1'b0;
        spr_bus_du_dmr1_st_r  <= 1'b0;
        spr_bus_du_dXr_te_r   <= 1'b0;
      end
      else if (spr_bus_ack_du_r) begin // end of cycle
        spr_du_wr_r           <= 1'b0;
        spr_bus_ack_du_r      <= 1'b0;
        spr_bus_du_dmr1_st_r  <= 1'b0;
        spr_bus_du_dXr_te_r   <= 1'b0;
      end
      else if (spr_bus_cs_du) begin
        spr_bus_ack_du_r <= 1'b1;
        spr_du_wr_r      <= spr_bus_we_o;
        // data
        if (spr_bus_we_o) begin
          spr_bus_du_dmr1_st_r  <= 1'b0;
          spr_bus_du_dXr_te_r   <= 1'b0;
        end
        else begin
          spr_bus_du_dmr1_st_r  <= spr_bus_cs_du_dmr1 & spr_dmr1_st;
          spr_bus_du_dXr_te_r   <= (spr_bus_cs_du_dsr & spr_dsr_te) | (spr_bus_cs_du_drr & spr_drr_te);
       end
      end
    end // at clock

    assign spr_bus_dat_du = {
                              {(OPTION_OPERAND_WIDTH - 1 - `OR1K_SPR_DMR1_ST){1'b0}}, // DU enabled: SPR BUS DAT DU
                              spr_bus_du_dmr1_st_r,                                   // DU enabled: SPR BUS DAT DU
                              {(`OR1K_SPR_DMR1_ST - 1 - `OR1K_SPR_DSR_TE){1'b0}},     // DU enabled: SPR BUS DAT DU
                              spr_bus_du_dXr_te_r,                                    // DU enabled: SPR BUS DAT DU
                              {`OR1K_SPR_DSR_TE{1'b0}}                                // DU enabled: SPR BUS DAT DU
                            };


    /* DMR1 */
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        spr_dmr1_st <= 1'b0;
      else if (spr_du_wr_r & spr_bus_cs_du_dmr1)
        spr_dmr1_st <= spr_bus_dat_o[`OR1K_SPR_DMR1_ST];
    end // @ clock


    /* DSR */
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        spr_dsr_te <= 1'b0;
      else if (spr_du_wr_r & spr_bus_cs_du_dsr)
        spr_dsr_te <= spr_bus_dat_o[`OR1K_SPR_DSR_TE];
    end // @ clock

    // Pick the traps-cause-stall bit out of the DSR
    assign du_trap_enable_o = spr_dsr_te;


    /* DRR */
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        spr_drr_te <= 1'b0;
      else if (spr_du_wr_r & spr_bus_cs_du_drr)
        spr_drr_te <= spr_bus_dat_o[`OR1K_SPR_DRR_TE];
      else if (wb_except_trap_i) // DU
        spr_drr_te <= 1'b1;
    end // @ clock


    //
    // Cases for stall CPU
    //   (!) When we perform transition to stall caused by external
    //       command or current step completion we generate pipe flushing
    //       AFTER the last instuction completes write back.
    //
    wire doing_wb = pstep[3] & (~wb_lsu_valid_miss_i);
    //
    wire du_cpu_stall_by_cmd      = doing_wb & du_stall_i;
    wire du_cpu_stall_by_stepping = doing_wb & stepping;
    wire du_cpu_stall_by_trap     = wb_except_trap_i;

    //
    // Generate 1-clok length pipe flusing signal from DU
    //   (a) We don't take into accaunt "except-trap" here, because
    //       "except-trap" causes pipe flushing by exception processing logic
    //   (b) When we perform transition to stall caused by external
    //       command or current step completion we generate pipe flushing
    //       AFTER the last instuction completes write back.
    //
    assign du_cpu_flush = (du_cpu_stall_by_cmd | du_cpu_stall_by_stepping);

    //
    // goes out to the debug interface and
    // comes back 1 cycle later via  du_stall_i
    //
    assign du_stall_o = du_cpu_stall_by_stepping | du_cpu_stall_by_trap; // DU
    // ---
    reg du_cpu_stall_r, du_cpu_unstall_r;
    // ---
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst) begin
        du_cpu_stall_r   <= 1'b0;
        du_cpu_unstall_r <= 1'b0;
      end
      else if (du_cpu_unstall_r) begin
        if (fetch_exception_taken_i) begin
          du_cpu_stall_r   <= 1'b0;
          du_cpu_unstall_r <= 1'b0;
        end
      end
      else if (du_cpu_stall_r) begin
        if (~du_stall_i) begin
          du_cpu_stall_r   <= 1'b0;
          du_cpu_unstall_r <= 1'b1;
        end
      end
      else if (du_cpu_stall_by_cmd | du_cpu_stall_by_stepping | du_cpu_stall_by_trap) begin
        du_cpu_stall_r   <= 1'b1;
        du_cpu_unstall_r <= 1'b0;
      end
    end // @ clock
    // ---
    assign du_cpu_stall   = du_cpu_stall_r;
    assign du_cpu_unstall = du_cpu_unstall_r;

    //
    // Record if NPC was written while we were stalled.
    // If so, we will use this value for restarting
    //
    reg du_npc_hold_r;
    // ---
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        du_npc_hold_r <= 1'b0;
      else if (du_cpu_unstall & fetch_exception_taken_i)
        du_npc_hold_r <= 1'b0;
      else if (du_npc_we)
        du_npc_hold_r <= 1'b1;
    end // @ clock
    // ---
    assign du_npc_hold = du_npc_hold_r;

    /* Indicate step-by-step execution */
    assign stepping = spr_dmr1_st & spr_dsr_te;

    reg [3:0] pstep_r;
    assign    pstep = pstep_r; // DU enabled

    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        pstep_r <= 4'b0000;
      else if (stepping) begin
        if (du_cpu_stall & (~du_stall_i)) // the condition is equal to stall->unstall one
          pstep_r <= 4'b0001;
        else if (pass_step_to_decode | pass_step_to_wb | pass_step_to_stall | doing_wb)
          pstep_r <= {pstep_r[2:0],1'b0};
      end
      else begin
        if (padv_wb_o)
          pstep_r <= 4'b1000; // 1-clock delayed padv-wb on regular pipe advancing
        else if (~wb_lsu_valid_miss_i)
          pstep_r <= 4'b0000; // 1-clock delayed padv-wb on regular pipe advancing
      end
    end // @ clock


    // Any "stepped_into_*" is
    //  (a) 1-clock delayed "ctrl_spr_wb_r"
    //  (b) 1-clock length
    //  (c) used for correct tracking "Next PC"

    // Indicate when we have stepped into exception processing
    // ---
    reg stepped_into_exception_r;
    // ---
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        stepped_into_exception_r <= 1'b0;
      else
        stepped_into_exception_r <= stepping & wb_an_except_i;
    end // @ clock
    // ---
    assign stepped_into_exception = stepped_into_exception_r; // DU enabled


    // Indicate when we have stepped into l.rfe processing
    // ---
    reg stepped_into_rfe_r;
    // ---
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        stepped_into_rfe_r <= 1'b0;
      else
        stepped_into_rfe_r <= stepping & wb_op_rfe_i;
    end // @ clock
    // ---
    assign stepped_into_rfe = stepped_into_rfe_r; // DU enabled


    // Indicate when we have stepped into delay slot processing
    // ---
    reg du_jump_or_branch_p; // store that previous step was jump/branch
    // ---
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        du_jump_or_branch_p <= 1'b0;
      else if (stepping) begin
        if (stepped_into_delay_slot)
          du_jump_or_branch_p <= 1'b0;
        else if (wb_jump_or_branch_i)
          du_jump_or_branch_p <= 1'b1;
      end
      else 
        du_jump_or_branch_p <= 1'b0;
    end // @ clock
    // ---
    reg stepped_into_delay_slot_r;
    // ---
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        stepped_into_delay_slot_r <= 1'b0;
      else
        stepped_into_delay_slot_r <= stepping & ctrl_spr_wb_r & du_jump_or_branch_p;
    end // @ clock
    // ---
    assign stepped_into_delay_slot = stepped_into_delay_slot_r; // DU enabled

  end // DU is enabled
  else begin : du_none

    // make ACK to SPR BUS
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        spr_bus_ack_du_r <= 1'b0; // DU disabled
      else if (spr_bus_ack_du_r)
        spr_bus_ack_du_r <= 1'b0; // DU disabled
      else if (spr_bus_cs_du)
        spr_bus_ack_du_r <= 1'b1; // DU disabled
    end
    // data to SPR BUS
    assign spr_bus_dat_du = 32'd0; // DU disabled
    // "move to/from Debug System"
    assign spr_bus_mXdbg  = 1'b0; // DU disabled


    // make ACK to Debug System
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        du_ack_o <= 1'b0; // DU disabled
      else if (du_ack_o)
        du_ack_o <= 1'b0; // DU disabled
      else if (du_stb_i)
        du_ack_o <= 1'b1; // DU disabled
    end // @ clock
    // data to Debug System
    assign du_dat_o = {OPTION_OPERAND_WIDTH{1'b0}}; // DU disabled


    // stall / unstall
    assign du_stall_o       = 1'b0; // DU disabled
    assign du_trap_enable_o = 1'b0; // DU disabled
    // ---
    assign du_npc_hold    = 1'b0; // DU disabled
    assign du_cpu_flush   = 1'b0; // DU disabled
    assign du_cpu_stall   = 1'b0; // DU disabled
    assign du_cpu_unstall = 1'b0; // DU disabled

    // step-by-step
    // ---
    assign stepping = 1'b0; // DU disabled
    assign pstep    = 4'd0; // DU disabled
    // ---
    assign stepped_into_delay_slot = 1'b0; // DU disabled
    assign stepped_into_exception  = 1'b0; // DU disabled
    assign stepped_into_rfe        = 1'b0; // DU disabled

  end // DU enabled/disabled

  endgenerate

endmodule // mor1kx_ctrl_marocchino
