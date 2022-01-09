###########################################################
# SPDX-License-Identifier: CERN-OHL-W-2.0
#
# Description: Simplistic makefile for running formal tests
#
# Copyright (C) 2021
#    Stafford Horne <shorne@gmail.com>
#
##########################################################$

TESTS := mor1kx_cache_lru \
	mor1kx_simple_dpram_sclk \
	mor1kx_true_dpram_sclk \
	mor1kx_icache \
	mor1kx_immu \
	mor1kx_store_buffer \
	mor1kx_fetch_cappuccino \
	mor1kx_decode \
	mor1kx_decode_execute_cappuccino \
	mor1kx_execute_alu \
	mor1kx_execute_ctrl_cappuccino \
	mor1kx_dmmu \
	mor1kx_dcache \
	mor1kx_lsu_cappuccino \
	mor1kx_pcu \
	mor1kx_pic \
	mor1kx_ticktimer \
	mor1kx_ctrl_cappuccino \
	mor1kx_rf_cappuccino \
	mor1kx_bus_if_wb32 \
	mor1kx_wb_mux_cappuccino \
	mor1kx_cpu_cappuccino \
	mor1kx


all: $(TESTS)
clean:
	rm -rf $(TESTS)

.PHONY: all clean $(TESTS)

RTL := ../../rtl/verilog

$(TESTS): % :
	sby -f $@.sby
