#!/bin/sh

set -x

mkdir -p $HOME/src/tools
mkdir -p $HOME/tools

# Get iverilog latest source, the version in trusty is no good
cd $HOME/src/tools
curl --remote-name --location \
  http://shorne.noip.me/downloads/verilog-10.2.tar.gz
tar xf verilog-10.2.tar.gz
cd verilog-10.2
./configure --prefix=$HOME/tools
make -j2
make install


