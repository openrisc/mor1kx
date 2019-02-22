#!/bin/sh

cd /tmp

git clone http://git.veripool.org/git/verilator
cd verilator
git checkout verilator_3_902

autoconf
./configure
make -j2
sudo make install

cd $TRAVIS_BUILD_DIR
