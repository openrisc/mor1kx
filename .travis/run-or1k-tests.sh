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
export CORE_ARGS="--pipeline=$PIPELINE $EXTRA_CORE_ARGS"
export TARGET=mor1kx_tb
export TARGET_ARGS="--tool=$SIM"
./runtests.sh $@
result=$?

if [ $result != 0 ] ; then
  cat runtests.log
fi
exit $result
