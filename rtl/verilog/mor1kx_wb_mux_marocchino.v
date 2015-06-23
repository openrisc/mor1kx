/* ****************************************************************************
  This Source Code Form is subject to the terms of the
  Open Hardware Description License, v. 1.0. If a copy
  of the OHDL was not distributed with this file, You
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: RF writeback mux for MAROCCHINO pipeline

  Derived from mor1kx_wb_mux_cappuccino

  Copyright (C) 2012 Julius Baxter <juliusbaxter@gmail.com>
  Copyright (C) 2015 Andrey Bacherov <avbacherov@opencores.org>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_wb_mux_marocchino
#(
  parameter OPTION_OPERAND_WIDTH = 32,
  parameter OPTION_RF_ADDR_WIDTH =  5
)
(
  // clock & reset
  input                                 clk,
  input                                 rst,

  // pipeline control signals
  input                                 padv_wb_i,
  input                                 pipeline_flush_i,

  // from ALU
  input      [OPTION_OPERAND_WIDTH-1:0] alu_nl_result_i,

  // from LSU
  input                                 exec_op_lsu_load_i,
  input                                 lsu_excepts_i,
  input      [OPTION_OPERAND_WIDTH-1:0] lsu_result_i,

  // MFSPR
  input                                 exec_op_mfspr_i,
  input      [OPTION_OPERAND_WIDTH-1:0] mfspr_dat_i,

  // destination address & write request flag
  input                                 exec_bubble_i,
  input      [OPTION_RF_ADDR_WIDTH-1:0] exec_rfd_adr_i,
  input                                 exec_rf_wb_i,

  // PC
  input      [OPTION_OPERAND_WIDTH-1:0] pc_exec_i,

  // Insn in delay slot indicator (exception processing)
  input                                 exec_op_branch_i,

  // set/clear flags
  input                                 lsu_atomic_flag_set_i,
  input                                 lsu_atomic_flag_clear_i,
  input                                 exec_flag_set_i,
  input                                 exec_flag_clear_i,
  input                                 exec_carry_set_i,
  input                                 exec_carry_clear_i,
  input                                 exec_overflow_set_i,
  input                                 exec_overflow_clear_i,

  // FPU related
  input         [`OR1K_FPCSR_WIDTH-1:0] exec_fpcsr_i,
  input                                 exec_fpcsr_set_i,

  // EXCEPTIONS
  //  input exceptions
  input                                 exec_except_ibus_err_i,
  input                                 exec_except_ipagefault_i,
  input                                 exec_except_itlb_miss_i,
  input                                 exec_except_ibus_align_i,
  input                                 exec_except_illegal_i,
  input                                 exec_except_syscall_i,
  input                                 exec_except_trap_i,
  input                                 lsu_except_dbus_err_i,
  input                                 lsu_except_dpagefault_i,
  input                                 lsu_except_dtlb_miss_i,
  input                                 lsu_except_dbus_align_i,
  input                                 exec_excepts_en_i,
  //  output exceptions
  output reg                            wb_except_ibus_err_o,
  output reg                            wb_except_ipagefault_o,
  output reg                            wb_except_itlb_miss_o,
  output reg                            wb_except_ibus_align_o,
  output reg                            wb_except_illegal_o,
  output reg                            wb_except_syscall_o,
  output reg                            wb_except_trap_o,
  output reg                            wb_except_dbus_o,
  output reg                            wb_except_dpagefault_o,
  output reg                            wb_except_dtlb_miss_o,
  output reg                            wb_except_align_o,
  output reg                            wb_excepts_en_o,

  // RFE processing
  input                                 doing_rfe_i,
  input                                 exec_op_rfe_i,
  output reg                            wb_op_rfe_o,

  // muxed output
  output reg [OPTION_OPERAND_WIDTH-1:0] pc_wb_o,
  output reg                            wb_delay_slot_o,
  output reg                            wb_atomic_flag_set_o,
  output reg                            wb_atomic_flag_clear_o,
  output reg                            wb_flag_set_o,
  output reg                            wb_flag_clear_o,
  output reg                            wb_carry_set_o,
  output reg                            wb_carry_clear_o,
  output reg                            wb_overflow_set_o,
  output reg                            wb_overflow_clear_o,
  output reg    [`OR1K_FPCSR_WIDTH-1:0] wb_fpcsr_o,
  output reg                            wb_fpcsr_set_o,
  output reg [OPTION_OPERAND_WIDTH-1:0] wb_result_o,
  output reg [OPTION_RF_ADDR_WIDTH-1:0] wb_rfd_adr_o,
  output reg                            wb_rf_wb_o
);

  // result
  always @(posedge clk) begin
    if (padv_wb_i & (~pipeline_flush_i)) begin
      if (exec_op_mfspr_i)
        wb_result_o <= mfspr_dat_i;
      else if (exec_op_lsu_load_i)
        wb_result_o <= lsu_result_i;
      else if (exec_rf_wb_i)
        wb_result_o <= alu_nl_result_i;
    end
  end // @clock

  // write back request
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      wb_rf_wb_o <= 1'b0;
    else if (pipeline_flush_i |
             (exec_op_lsu_load_i & lsu_excepts_i))
      wb_rf_wb_o <= 1'b0;
    else if (padv_wb_i)
      wb_rf_wb_o <= exec_rf_wb_i;
  end // @clock

  // address of destination register & PC
  always @(posedge clk) begin
    if (padv_wb_i & 
        (~pipeline_flush_i) & (~exec_bubble_i)) begin
      wb_rfd_adr_o <= exec_rfd_adr_i;
      pc_wb_o      <= pc_exec_i;
    end 
  end // @clock

  //-------------------------------------------------------//
  // Remember when we're in a delay slot in execute stage. //
  // For correct exception processing                      //
  //-------------------------------------------------------//
  reg store_delay_slot;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      store_delay_slot <= 1'b0;
      wb_delay_slot_o  <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      store_delay_slot <= 1'b0;
      wb_delay_slot_o  <= 1'b0;
    end
    else if (padv_wb_i & (~exec_bubble_i)) begin
      store_delay_slot <= exec_op_branch_i;
      wb_delay_slot_o  <= store_delay_slot;
    end
  end // @clock

  // FPU related
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      wb_fpcsr_o     <= {`OR1K_FPCSR_WIDTH{1'b0}};
      wb_fpcsr_set_o <= 1'b0;
    end
    else if (pipeline_flush_i |
             (padv_wb_i & exec_bubble_i)) begin
      wb_fpcsr_o     <= {`OR1K_FPCSR_WIDTH{1'b0}};
      wb_fpcsr_set_o <= 1'b0;
    end
    else if (padv_wb_i) begin
      wb_fpcsr_o     <= exec_fpcsr_i;
      wb_fpcsr_set_o <= exec_fpcsr_set_i;
    end
  end // @clock

  // flag/carry/overflow
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      wb_atomic_flag_set_o   <= 1'b0;
      wb_atomic_flag_clear_o <= 1'b0;
      wb_flag_set_o          <= 1'b0;
      wb_flag_clear_o        <= 1'b0;
      wb_carry_set_o         <= 1'b0;
      wb_carry_clear_o       <= 1'b0;
      wb_overflow_set_o      <= 1'b0;
      wb_overflow_clear_o    <= 1'b0;
    end
    else if (pipeline_flush_i | 
             (padv_wb_i & exec_bubble_i)) begin
      wb_atomic_flag_set_o   <= 1'b0;
      wb_atomic_flag_clear_o <= 1'b0;
      wb_flag_set_o          <= 1'b0;
      wb_flag_clear_o        <= 1'b0;
      wb_carry_set_o         <= 1'b0;
      wb_carry_clear_o       <= 1'b0;
      wb_overflow_set_o      <= 1'b0;
      wb_overflow_clear_o    <= 1'b0;
    end
    else if (padv_wb_i) begin
      wb_atomic_flag_set_o   <= lsu_atomic_flag_set_i;
      wb_atomic_flag_clear_o <= lsu_atomic_flag_clear_i;
      wb_flag_set_o          <= exec_flag_set_i;
      wb_flag_clear_o        <= exec_flag_clear_i;
      wb_carry_set_o         <= exec_carry_set_i;
      wb_carry_clear_o       <= exec_carry_clear_i;
      wb_overflow_set_o      <= exec_overflow_set_i;
      wb_overflow_clear_o    <= exec_overflow_clear_i;
    end
  end // @clock

  // EXCEPTIONS & RFE
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      wb_except_ibus_err_o   <= 1'b0;
      wb_except_ipagefault_o <= 1'b0;
      wb_except_itlb_miss_o  <= 1'b0;
      wb_except_ibus_align_o <= 1'b0;
      wb_except_illegal_o    <= 1'b0;
      wb_except_syscall_o    <= 1'b0;
      wb_except_trap_o       <= 1'b0;
      wb_except_dbus_o       <= 1'b0;
      wb_except_dpagefault_o <= 1'b0;
      wb_except_dtlb_miss_o  <= 1'b0;
      wb_except_align_o      <= 1'b0;
      wb_excepts_en_o        <= 1'b0;
      // RFE
      wb_op_rfe_o            <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      wb_except_ibus_err_o   <= 1'b0;
      wb_except_ipagefault_o <= 1'b0;
      wb_except_itlb_miss_o  <= 1'b0;
      wb_except_ibus_align_o <= 1'b0;
      wb_except_illegal_o    <= 1'b0;
      wb_except_syscall_o    <= 1'b0;
      wb_except_trap_o       <= 1'b0;
      wb_except_dbus_o       <= 1'b0;
      wb_except_dpagefault_o <= 1'b0;
      wb_except_dtlb_miss_o  <= 1'b0;
      wb_except_align_o      <= 1'b0;
      wb_excepts_en_o        <= 1'b0;
      // RFE
      wb_op_rfe_o            <= 1'b0;
    end
    else if (padv_wb_i) begin
      wb_except_ibus_err_o   <= exec_except_ibus_err_i;
      wb_except_ipagefault_o <= exec_except_ipagefault_i;
      wb_except_itlb_miss_o  <= exec_except_itlb_miss_i;
      wb_except_ibus_align_o <= exec_except_ibus_align_i;
      wb_except_illegal_o    <= exec_except_illegal_i;
      wb_except_syscall_o    <= exec_except_syscall_i;
      wb_except_trap_o       <= exec_except_trap_i;
      wb_except_dbus_o       <= lsu_except_dbus_err_i;
      wb_except_dpagefault_o <= lsu_except_dpagefault_i;
      wb_except_dtlb_miss_o  <= lsu_except_dtlb_miss_i;
      wb_except_align_o      <= lsu_except_dbus_align_i;
      wb_excepts_en_o        <= exec_excepts_en_i;
      // RFE
      wb_op_rfe_o            <= exec_op_rfe_i;
    end
  end // @clock

endmodule // mor1kx_wb_mux_marocchino
