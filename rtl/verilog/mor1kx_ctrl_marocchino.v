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
  input                                 exec_an_except_i,
  input                                 dcod_valid_i,
  input                                 exec_valid_i,
  output                                pipeline_flush_o,
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

  // Track branch address for exception processing support
  input                                 dcod_do_branch_i,
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_do_branch_target_i,
  //input                                 dcod_jump_or_branch_i,
  // Support IBUS error handling in CTRL
  input                                 exec_jump_or_branch_i,
  input      [OPTION_OPERAND_WIDTH-1:0] pc_exec_i,

  // Debug System accesses CPU SPRs through DU
  input                          [15:0] du_addr_i,
  input                                 du_stb_i,
  input      [OPTION_OPERAND_WIDTH-1:0] du_dat_i,
  input                                 du_we_i,
  output reg [OPTION_OPERAND_WIDTH-1:0] du_dat_o,
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
  input                                 wb_an_interrupt_i,

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

  //  # particular IFETCH exception flags
  input                                 wb_except_ibus_err_i,
  input                                 wb_except_itlb_miss_i,
  input                                 wb_except_ipagefault_i,
  input                                 wb_except_ibus_align_i,
  input      [OPTION_OPERAND_WIDTH-1:0] wb_lsu_except_addr_i,
  //  # particular DECODE exception flags
  input                                 wb_except_illegal_i,
  input                                 wb_except_syscall_i,
  input                                 wb_except_trap_i,
  //  # combined DECODE/IFETCH exceptions flag
  input                                 wb_fd_an_except_i,

  //  # particular LSU exception flags
  input                                 wb_except_dbus_err_i,
  input                                 wb_except_dtlb_miss_i,
  input                                 wb_except_dpagefault_i,
  input                                 wb_except_dbus_align_i,
  //  # combined LSU exceptions flag
  input                                 wb_an_except_lsu_i,
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
  reg [OPTION_OPERAND_WIDTH-1:0]    spr_evbar;

  // FPU Control & Status Register
  // and related exeption signals
  reg [`OR1K_FPCSR_WIDTH-1:0]       spr_fpcsr;

  reg [OPTION_OPERAND_WIDTH-1:0]    spr_ppc;
  reg [OPTION_OPERAND_WIDTH-1:0]    spr_npc;

  reg [OPTION_OPERAND_WIDTH-1:0]    exception_pc_addr;


  /* DU internal control signals */
  // SPR BUS acceess to DU's control registers
  wire                              spr_bus_cs_du;  // "chip select" for DU
  reg                               spr_bus_ack_du;
  reg                        [31:0] spr_bus_dat_du;
  // Access to NextPC SPR from Debug System through SPR BUS
  wire                              du_npc_we;
  reg                               du_npc_hold; // till restart command from Debug System
  // stall / unstall
  reg                               du_cpu_flush_r;
  reg                               du_cpu_stall_r;
  reg                               du_cpu_unstall_r;
  // step-by-step execution
  wire                              stepping;
  reg                         [2:0] pstep;
  wire                              stepped_into_delay_slot;
  reg                               stepped_into_exception;
  reg                               stepped_into_rfe;


  /* For SPR BUS transactions */
  reg                               spr_bus_wait_r;  // wait SPR ACK regardless on access validity
  reg                               spr_bus_mXspr_r; // access by l.mf(t)spr command indicator (for write back push)
  reg                               spr_bus_access_du_r; // access from Debug System
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

  // collect exceptions from all units
  wire exception_re = wb_fd_an_except_i        |
                      wb_except_overflow_div_i | wb_except_overflow_1clk_i |
                      wb_except_fp32_cmp_i     | wb_except_fp64_cmp_i      |
                      wb_except_fpxx_arith_i   |
                      wb_an_except_lsu_i       | sbuf_err_i                |
                      wb_an_interrupt_i;

  // Store exception vector
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      exception_pc_addr <= {19'd0,`OR1K_RESET_VECTOR,8'd0};
    else if (exception_re) begin
      // synthesis parallel_case full_case
      casez({wb_except_itlb_miss_i,
             wb_except_ipagefault_i,
             wb_except_ibus_err_i,
             wb_except_illegal_i,
             wb_except_dbus_align_i,
             wb_except_ibus_align_i,
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
        15'b1??????????????: exception_pc_addr <= spr_evbar | {19'd0,`OR1K_ITLB_VECTOR,8'd0};
        15'b01?????????????: exception_pc_addr <= spr_evbar | {19'd0,`OR1K_IPF_VECTOR,8'd0};
        15'b001????????????: exception_pc_addr <= spr_evbar | {19'd0,`OR1K_BERR_VECTOR,8'd0};
        15'b0001???????????: exception_pc_addr <= spr_evbar | {19'd0,`OR1K_ILLEGAL_VECTOR,8'd0};
        15'b00001??????????,
        15'b000001?????????: exception_pc_addr <= spr_evbar | {19'd0,`OR1K_ALIGN_VECTOR,8'd0};
        15'b0000001????????: exception_pc_addr <= spr_evbar | {19'd0,`OR1K_SYSCALL_VECTOR,8'd0};
        15'b00000001???????: exception_pc_addr <= spr_evbar | {19'd0,`OR1K_DTLB_VECTOR,8'd0};
        15'b000000001??????: exception_pc_addr <= spr_evbar | {19'd0,`OR1K_DPF_VECTOR,8'd0};
        15'b0000000001?????: exception_pc_addr <= spr_evbar | {19'd0,`OR1K_TRAP_VECTOR,8'd0};
        15'b00000000001????: exception_pc_addr <= spr_evbar | {19'd0,`OR1K_BERR_VECTOR,8'd0};
        15'b000000000001???: exception_pc_addr <= spr_evbar | {19'd0,`OR1K_RANGE_VECTOR,8'd0};
        15'b0000000000001??: exception_pc_addr <= spr_evbar | {19'd0,`OR1K_FP_VECTOR,8'd0};
        15'b00000000000001?: exception_pc_addr <= spr_evbar | {19'd0,`OR1K_INT_VECTOR,8'd0};
        15'b000000000000001: exception_pc_addr <= spr_evbar | {19'd0,`OR1K_TT_VECTOR,8'd0};
        default:             exception_pc_addr <= spr_evbar | {19'd0,`OR1K_RESET_VECTOR,8'd0};
      endcase // casex (...
    end
  end // @ clock

  // flag to select l.rfe related branch vector
  reg doing_rfe_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      doing_rfe_r <= 1'b0;
    else if ((doing_rfe_r | du_cpu_unstall_r) & fetch_exception_taken_i)
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
    else if ((doing_exception_r | du_cpu_unstall_r) & fetch_exception_taken_i)
      doing_exception_r <= 1'b0;
    else if (exception_re)
      doing_exception_r <= 1'b1;
  end // @ clock

  // To FETCH:
  //   Flag to use DU/exceptions/rfe provided address
  assign ctrl_branch_exception_o = du_cpu_unstall_r | doing_exception_r | doing_rfe_r;
  //   DU/exceptions/rfe provided address itself
  assign ctrl_branch_except_pc_o = du_cpu_unstall_r  ? spr_npc           :
                                   doing_exception_r ? exception_pc_addr :
                                                       spr_epcr;


  //--------------------------------//
  // special flag that WB is active //
  //--------------------------------//

  // 1-clock delayed padv-wb-o
  reg  doing_wb_r;  // just for doing-wb
  wire doing_wb = doing_wb_r & (~wb_lsu_valid_miss_i);
  // MAROCCHINO_TODO: stepped_into* for DU in exception case?
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      doing_wb_r <= 1'b0;
    else if (pipeline_flush_o)
      doing_wb_r <= 1'b0;
    else if (padv_wb_o)
      doing_wb_r <= 1'b1;
    else if (doing_wb)
      doing_wb_r <= 1'b0;
  end // @ clock

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

  // Pipeline flush by DU/exceptions/rfe
  assign pipeline_flush_o = du_cpu_flush_r | exception_re | wb_op_rfe_i;

  // Advance IFETCH
  //  (a) without DU control
  wire   padv_fetch   = (dcod_valid_i | (~dcod_insn_valid_i)) & (~spr_bus_wait_r) & (~fetch_an_except_i) & (~exec_an_except_i);
  //  (b) for step-by-step execution
  //        - pay attention that "*_an_except" doesn't make sense here
  //      because of step-by-step execution
  //        - but we block execution if SPR BUS is active, because it
  //      could be request from Debug System
  wire   padv_fetch_s = pstep[0] & (~dcod_insn_valid_i) & (~spr_bus_wait_r);
  //  (!) signal to pass step from IFETCH to DECODE
  wire   pass_step_to_decode = pstep[0] & dcod_insn_valid_i & (~spr_bus_wait_r); // for DU
  //  (c) with DU control (and output)
  assign padv_fetch_o = du_cpu_stall_r ? 1'b0         :
                        stepping       ? padv_fetch_s :
                                         padv_fetch;

  // Advance DECODE->EXECUTE latches
  //  (a) without DU control
  wire   padv_decode   = dcod_valid_i & dcod_insn_valid_i & (~spr_bus_wait_r) & (~exec_an_except_i);
  //  (b) for step-by-step execution
  wire   padv_decode_s = pstep[1] & padv_decode;
  //  (!) signal to pass step from DECODE to WB
  wire   pass_step_to_wb = padv_decode_s; // for DU
  //  (c) with DU control (and output)
  assign padv_decode_o = du_cpu_stall_r ? 1'b0          :
                         stepping       ? padv_decode_s :
                                          padv_decode;

  // Advance Write Back latches
  //  (a) without DU control
  wire   padv_wb   = (exec_valid_i & (~spr_bus_wait_r) & (~wb_lsu_valid_miss_i)) | (spr_bus_ack_r & spr_bus_mXspr_r);
  //  (b) for step-by-step execution
  wire   padv_wb_s = pstep[2] & padv_wb;
  //  (!) complete the step
  wire   pass_step_to_stall = padv_wb_s; // for DU
  //  (b) with DU control (and output)
  assign padv_wb_o = du_cpu_stall_r ? 1'b0      :
                     stepping       ? padv_wb_s :
                                      padv_wb;


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
    else if (exception_re) begin
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
    else if (exception_re)
      spr_esr <= spr_sr; // by exceptions
    else if (spr_sys_group_cs & (`SPR_OFFSET(spr_bus_addr_o) == `SPR_OFFSET(`OR1K_SPR_ESR0_ADDR)) &
             spr_sys_group_wr_r)
      spr_esr <= spr_bus_dat_o[SPR_SR_WIDTH-1:0];
  end // @ clock


  // PC before and after WB
  wire [OPTION_OPERAND_WIDTH-1:0] pc_pre_wb = pc_wb_i - 3'd4;
  wire [OPTION_OPERAND_WIDTH-1:0] pc_nxt_wb = pc_wb_i + 3'd4;

  // Exception PC

  //   ## Store address of latest jump/branch instruction
  //      specially for IBUS error handling
  reg [OPTION_OPERAND_WIDTH-1:0] last_jump_or_branch_pc;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      last_jump_or_branch_pc <= {OPTION_OPERAND_WIDTH{1'b0}};
    else if (pipeline_flush_o)
      last_jump_or_branch_pc <= {OPTION_OPERAND_WIDTH{1'b0}};
    else if (padv_wb_o & exec_jump_or_branch_i)
      last_jump_or_branch_pc <= pc_exec_i;
  end // @clock


  //   E-P-C-R update
  always @(posedge clk`OR_ASYNC_RST) begin
    if (rst) begin
      spr_epcr <= {OPTION_OPERAND_WIDTH{1'b0}};
    end
    else if (exception_re) begin
      // Syscall is a special case, we return back to the instruction _after_
      // the syscall instruction, unless the syscall was in a delay slot
      if (wb_except_syscall_i)
        spr_epcr <= wb_delay_slot_i ? pc_pre_wb : pc_nxt_wb;
      else if (wb_except_ibus_err_i)
        spr_epcr <= last_jump_or_branch_pc; // IBUS error
      else if (sbuf_err_i)
        spr_epcr <= sbuf_epcr_i;
      // Don't update EPCR on software breakpoint
      else if (~wb_except_trap_i)
        spr_epcr <= wb_delay_slot_i ? pc_pre_wb : pc_wb_i;
    end
    else if (spr_sys_group_cs & (`SPR_OFFSET(spr_bus_addr_o) == `SPR_OFFSET(`OR1K_SPR_EPCR0_ADDR)) &
             spr_sys_group_wr_r) begin
      spr_epcr <= spr_bus_dat_o;
    end
  end // @ clock


  // Exception Effective Address
  wire lsu_err = wb_except_dbus_align_i | wb_except_dtlb_miss_i | wb_except_dpagefault_i;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      spr_eear <= {OPTION_OPERAND_WIDTH{1'b0}};
    else if (exception_re) begin
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


  // Target of last taken branch
  reg [OPTION_OPERAND_WIDTH-1:0] last_branch_target;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      last_branch_target <= {OPTION_OPERAND_WIDTH{1'b0}};
    else if (padv_decode_o & dcod_do_branch_i)
      last_branch_target <= dcod_do_branch_target_i;
  end // @ clock


  // NPC for SPR (write accesses implemented for Debug System only)
  assign du_npc_we = (spr_sys_group_cs & (`SPR_OFFSET(spr_bus_addr_o) == `SPR_OFFSET(`OR1K_SPR_NPC_ADDR)) &
                      spr_sys_group_wr_r & spr_bus_access_du_r);
  // --- Actually it is used just to restart CPU after salling by DU
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      spr_npc <= OPTION_RESET_PC;
    else if (du_npc_we)          // Write restart PC and ...
      spr_npc <= du_dat_i;
    else if (~du_npc_hold) begin // ... hold it till restart command from Debug System
      if (ctrl_spr_wb_r) begin // Track NPC
        spr_npc <= wb_except_trap_i ? pc_wb_i            :
                   wb_delay_slot_i  ? last_branch_target :
                                      pc_nxt_wb;
      end
      else begin
        // any "stepped_into_*" is 1-clock delayed "doing_wb"
        spr_npc <= stepped_into_exception  ? exception_pc_addr  :
                   stepped_into_rfe        ? spr_epcr           :
                   stepped_into_delay_slot ? last_branch_target :
                                             spr_npc;
      end
    end
  end // @ clock

  // Exception Vector Address
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      spr_evbar <= {OPTION_OPERAND_WIDTH{1'b0}};
    else if (spr_sys_group_cs & (`SPR_OFFSET(spr_bus_addr_o) == `SPR_OFFSET(`OR1K_SPR_EVBAR_ADDR)) &
             spr_sys_group_wr_r)
      spr_evbar <= {spr_bus_dat_o[OPTION_OPERAND_WIDTH-1:13], 13'd0};
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
      `SPR_OFFSET(`OR1K_SPR_EVBAR_ADDR)   : spr_sys_group_dat = spr_evbar;
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
                       spr_bus_ack_mac_i     | spr_bus_ack_du     |
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

    // Generate ack back to the debug interface bus
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst) begin
        spr_bus_access_du_r <= 1'b0;
        du_ack_o            <= 1'b0;
      end
      else if (du_ack_o) begin
        spr_bus_access_du_r <= 1'b0;
        du_ack_o            <= 1'b0;
      end
      else if (spr_bus_access_du_r) begin
        if (spr_bus_ack) begin // DU uses non-registered SPR BUS sources
          spr_bus_access_du_r <= 1'b0;
          du_ack_o            <= 1'b1;
        end
      end
      else if (take_access_du) begin
        spr_bus_access_du_r <= 1'b1;
        du_ack_o            <= 1'b0;
      end
    end // @ clock

    // Data back to the debug bus
    always @(posedge clk) begin
      if (spr_bus_ack & spr_bus_access_du_r & (~spr_bus_we_o)) // DU uses non-registered SPR BUS sources
        du_dat_o <= spr_bus_dat_mux; // DU uses non-registered SPR BUS sources
    end


    /* DU's Control registers and SPR BUS access cycle */

    reg [31:0] spr_dmr1;
    reg [31:0] spr_dmr2;
    reg [31:0] spr_dsr;
    reg [31:0] spr_drr;

    wire spr_bus_cs_du_dmr1 = (`SPR_OFFSET(spr_bus_addr_o) == `SPR_OFFSET(`OR1K_SPR_DMR1_ADDR));
    wire spr_bus_cs_du_dmr2 = (`SPR_OFFSET(spr_bus_addr_o) == `SPR_OFFSET(`OR1K_SPR_DMR2_ADDR));
    wire spr_bus_cs_du_dsr  = (`SPR_OFFSET(spr_bus_addr_o) == `SPR_OFFSET(`OR1K_SPR_DSR_ADDR));
    wire spr_bus_cs_du_drr  = (`SPR_OFFSET(spr_bus_addr_o) == `SPR_OFFSET(`OR1K_SPR_DRR_ADDR));

    reg spr_du_wr_r;

    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst) begin
        spr_du_wr_r    <=  1'b0;
        spr_bus_ack_du <=  1'b0;
        spr_bus_dat_du <= 32'd0;
      end
      else if (spr_bus_ack_du) begin // end of cycle
        spr_du_wr_r    <=  1'b0;
        spr_bus_ack_du <=  1'b0;
        spr_bus_dat_du <= 32'd0;
      end
      else if (spr_bus_cs_du) begin
        spr_bus_ack_du <= 1'b1;
        spr_du_wr_r    <= spr_bus_we_o;
        // data
        if (spr_bus_we_o) begin
          spr_bus_dat_du <= 32'd0;
        end
        else begin
          spr_bus_dat_du <= spr_bus_cs_du_dmr1 ? spr_dmr1 :
                            spr_bus_cs_du_dmr2 ? spr_dmr2 :
                            spr_bus_cs_du_dsr  ? spr_dsr  :
                            spr_bus_cs_du_drr  ? spr_drr  :
                                                 32'd0;
        end
      end
    end // at clock


    /* DMR1 */
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        spr_dmr1 <= 32'd0;
      else if (spr_du_wr_r & spr_bus_cs_du_dmr1)
        spr_dmr1[23:0] <= spr_bus_dat_o[23:0];
    end // @ clock


    /* DMR2 */
    always @(posedge clk)
      spr_dmr2 <= 0;


    /* DSR */
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        spr_dsr <= 32'd0;
      else if (spr_du_wr_r & spr_bus_cs_du_dsr)
        spr_dsr[13:0] <= spr_bus_dat_o[13:0];
    end // @ clock

    // Pick the traps-cause-stall bit out of the DSR
    assign du_trap_enable_o = spr_dsr[`OR1K_SPR_DSR_TE];


    /* DRR */
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        spr_drr <= 32'd0;
      else if (spr_du_wr_r & spr_bus_cs_du_drr)
        spr_drr[13:0] <= spr_bus_dat_o[13:0];
      else if (wb_except_trap_i) // DU
        spr_drr[`OR1K_SPR_DRR_TE] <= 1'b1;
    end // @ clock


    //
    // Cases for stall CPU
    //   (!) When we perform transition to stall caused by external
    //       command or current step completion we generate pipe flushing
    //       AFTER the last instuction completes write back.
    //       For step completion it means that "doing_wb" is equal
    //       to hypotetic pstep[3]
    //
    wire du_cpu_stall_by_cmd      = doing_wb & du_stall_i;
    wire du_cpu_stall_by_stepping = doing_wb & stepping;
    wire du_spu_stall_by_trap     = wb_except_trap_i;

    //
    // Generate 1-clok length pipe flusing signal from DU
    //   (a) We don't take into accaunt "except-trap" here, because
    //       "except-trap" causes pipe flushing by exception processing logic
    //   (b) When we perform transition to stall caused by external
    //       command or current step completion we generate pipe flushing
    //       AFTER the last instuction completes write back.
    //   (c) If cpu already stalled we prevent manipulation with the register
    //       because pipes were flushed previously
    //
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        du_cpu_flush_r <= 1'b0;
      else if (du_cpu_stall_r) // pipes were flushed previously
        du_cpu_flush_r <= 1'b0;
      else if (du_cpu_flush_r) // 1-clock lenght (eq. to exceptions/rfe pocessing)
        du_cpu_flush_r <= 1'b0;
      else if (du_cpu_stall_by_cmd | du_cpu_stall_by_stepping)
        du_cpu_flush_r <= 1'b1;
    end // @ clock


    /* goes out to the debug interface and comes back 1 cycle later
       via du_stall_i */
    assign du_stall_o = du_cpu_stall_by_stepping | du_spu_stall_by_trap; // DU

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
      else if (du_cpu_stall_by_cmd | du_cpu_stall_by_stepping | du_spu_stall_by_trap) begin
        du_cpu_stall_r   <= 1'b1;
        du_cpu_unstall_r <= 1'b0;
      end
    end // @ clock

    /* record if NPC was written while we were stalled.
       If so, we will use this value for restarting */
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        du_npc_hold <= 1'b0;
      else if (du_cpu_unstall_r & fetch_exception_taken_i)
        du_npc_hold <= 1'b0;
      else if (du_npc_we)
        du_npc_hold <= 1'b1;
    end // @ clock


    /* Indicate step-by-step execution */
    assign stepping = spr_dmr1[`OR1K_SPR_DMR1_ST] & spr_dsr[`OR1K_SPR_DSR_TE];

    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        pstep <= 3'h0;
      else if (stepping & du_cpu_stall_r & (~du_stall_i))
        // (!) ^^^ the condition is equal to stall->unstall one
        pstep <= 3'h1;
      else if (pass_step_to_decode | pass_step_to_wb | pass_step_to_stall)
        pstep <= {pstep[1:0],1'b0};
    end // @ clock

    //
    // Indicate when we have stepped into exception processing
    // (for correct tracking "Next PC")
    // 1-clock length
    //
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        stepped_into_exception <= 1'b0;
      else
        stepped_into_exception <= stepping & exception_re;
    end // @ clock

    //
    // Indicate when we have stepped into l.rfe processing
    // (for correct tracking "Next PC")
    // 1-clock length
    //
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        stepped_into_rfe <= 1'b0;
      else
        stepped_into_rfe <= stepping & wb_op_rfe_i;
    end // @ clock

    //
    // Indicate when we have stepped into delay slot processing
    // (for correct tracking "Next PC")
    // 1-clock length
    //   bit [0] : latch "jump / taken branch" flag
    //   bit [1] : completion of step with "jump / taken branch" instruction
    //   bit [2] : completion of delay slot instruction ("stepped_into_delay_slot" 1-clock pulse)
    //
    reg [2:0] branch_step;
    // ---
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        branch_step <= 3'd0;
      else if (~stepping)
        branch_step <= 3'd0;
      else begin // step-by-step execution
        if (branch_step[2])
          branch_step <= 3'd0;
        else if (|branch_step[1:0]) begin
          if(du_cpu_stall_by_stepping)
            branch_step <= {branch_step[1:0],1'b0};
        end
        else if (padv_decode_s & dcod_do_branch_i)
          branch_step <= 3'd1;
      end
    end // @ clock
    // ---
    assign stepped_into_delay_slot = branch_step[2];

  end // DU is enabled
  else begin : du_none

    // make ACK to SPR BUS
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        spr_bus_ack_du <= 1'b0;
      else if (spr_bus_ack_du)
        spr_bus_ack_du <= 1'b0;
      else if (spr_bus_cs_du)
        spr_bus_ack_du <= 1'b1;
    end

    // make ACK to Debug System
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        du_ack_o <= 1'b0;
      else if (du_ack_o)
        du_ack_o <= 1'b0;
      else if (du_stb_i)
        du_ack_o <= 1'b1;
    end

    // data to output to SPR BUS and to Debug System
    always @(posedge clk) begin
      spr_bus_access_du_r <=  1'b0;
      spr_bus_dat_du      <= 32'd0;
      du_dat_o            <= {OPTION_OPERAND_WIDTH{1'b0}};
    end

    // stall / unstall
    assign du_stall_o       = 1'b0;
    assign du_trap_enable_o = 1'b0;
    // ---
    always @(posedge clk) begin
      du_npc_hold      <= 1'b0;
      du_cpu_flush_r   <= 1'b0;
      du_cpu_stall_r   <= 1'b0;
      du_cpu_unstall_r <= 1'b0;
    end // @ clock

    // step-by-step
    assign stepping = 1'b0;
    assign stepped_into_delay_slot = 1'b0;
    // ---
    always @(posedge clk) begin
      pstep                  <= 3'd0;
      stepped_into_exception <= 1'b0;
      stepped_into_rfe       <= 1'b0;
    end // @ clock

  end // DU enabled/none

  endgenerate

endmodule // mor1kx_ctrl_marocchino
