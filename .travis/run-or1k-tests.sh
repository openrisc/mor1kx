#!/bin/sh

set -x

PATH="$HOME/tools/or1k-elf/bin:${PATH}"
PATH="$HOME/tools/bin:${PATH}"
export PATH

cd $HOME/src/tools/or1k-tests/native
./runtests.sh $PIPELINE

if [ $? != 0 ] ; then
  cat runtests.log
fi
