#!/bin/sh

set -x

PATH="$HOME/tools/or1k-elf/bin:${PATH}"
PATH="$HOME/tools/bin:${PATH}"
export PATH

# allow overriding root dir if we aren't running in travis
if [ -z $OR1K_TESTS_ROOT ] ; then
  OR1K_TESTS_ROOT=$HOME/src/tools/or1k-tests
fi

cd $OR1K_TESTS_ROOT/native
export CORE_ARGS="--pipeline=$PIPELINE"
export SIM_ARGS="--sim=$SIM"
./runtests.sh $@

if [ $? != 0 ] ; then
  cat runtests.log
fi
