#!/bin/sh

verilator --lint-only rtl/verilog/*.v +incdir+rtl/verilog
