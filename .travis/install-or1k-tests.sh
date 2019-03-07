#!/bin/sh

set -x

mkdir -p $HOME/src/tools
mkdir -p $HOME/tools

# Install the required sim
$TRAVIS_BUILD_DIR/.travis/install-${SIM}.sh

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

# Setup fusesoc and add the cores required by or1k-tests
fusesoc init -y
fusesoc library add mor1kx-generic https://github.com/stffrdhrn/mor1kx-generic.git
fusesoc library add intgen https://github.com/stffrdhrn/intgen.git
fusesoc library add mor1kx $TRAVIS_BUILD_DIR

