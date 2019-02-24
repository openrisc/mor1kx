#!/bin/sh

export PATH=$HOME/tools/bin:$PATH

verilator --lint-only rtl/verilog/*.v +incdir+rtl/verilog
