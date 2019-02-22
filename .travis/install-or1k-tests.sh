#!/bin/sh

set -x

mkdir -p $HOME/src/cores
mkdir -p $HOME/src/tools
mkdir -p $HOME/tools

# Get our toolchain
cd $HOME/src/tools
curl --remote-name --location \
  https://github.com/stffrdhrn/gcc/releases/download/or1k-9.0.0-20181113/or1k-elf-9.0.0-20181112.tar.xz
tar xC $HOME/tools -f $HOME/src/tools/or1k-elf-9.0.0-20181112.tar.xz

PATH="$HOME/tools/or1k-elf/bin:${PATH}"

# Get iverilog latest source, the version in trusty is no good
cd $HOME/src/tools
curl --remote-name --location \
  http://shorne.noip.me/downloads/verilog-10.2.tar.gz
tar xf verilog-10.2.tar.gz
cd verilog-10.2
./configure
make
sudo make install

export PATH

cd $HOME/src/tools
git clone https://github.com/openrisc/or1k-tests.git ;\
cd or1k-tests/native
make

# Get the cores for our test to run (in the future these should be in fusesoc)
cd $HOME/src/cores
git clone https://github.com/stffrdhrn/mor1kx-generic.git
git clone https://github.com/stffrdhrn/intgen.git

# Setup fusesoc
sudo pip3 install fusesoc
fusesoc init -y

echo '[main]' >> $HOME/.config/fusesoc/fusesoc.conf
echo "cores_root = $HOME/src/cores" >> $HOME/.config/fusesoc/fusesoc.conf
echo "  $TRAVIS_BUILD_DIR" >> $HOME/.config/fusesoc/fusesoc.conf

