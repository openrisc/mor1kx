###########################################################
# This Source Code Form is subject to the terms of the
# Open Hardware Description License, v. 1.0. If a copy
# of the OHDL was not distributed with this file, You
# can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt
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
	mor1kx_icache

all: $(TESTS)
clean:
	rm -rf $(TESTS)

.PHONY: all clean $(TESTS)

RTL := ../../rtl/verilog

$(TESTS): % : $(RTL)/%.v
	sby -f $@.sby
