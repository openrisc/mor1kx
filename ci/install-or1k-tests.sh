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

# Get our toolchain
cd $HOME/src/tools
curl --remote-name --location \
  https://github.com/stffrdhrn/gcc/releases/download/or1k-9.0.0-20181113/or1k-elf-9.0.0-20181112.tar.xz
tar xC $HOME/tools -f $HOME/src/tools/or1k-elf-9.0.0-20181112.tar.xz

PATH="$HOME/tools/or1k-elf/bin:${PATH}"
export PATH

# Download and compile or1k-tests
cd $HOME/src/tools
git clone https://github.com/openrisc/or1k-tests.git ;\
cd or1k-tests/native
make -j2
