#!/bin/sh

set -x

mkdir -p $HOME/src/tools
mkdir -p $HOME/tools

# Get required version of verilator
cd $HOME/src/tools

git clone http://git.veripool.org/git/verilator
cd verilator
git checkout verilator_3_902

autoconf
./configure --prefix=$HOME/tools
make -j2
make install

