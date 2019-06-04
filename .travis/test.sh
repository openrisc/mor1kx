#!/bin/bash 

apt-get update && apt-get install -y curl

export TRAVIS_BUILD_DIR=/src
export HOME=/tmp

cd /src
echo "Installing test scripts"
./.travis/install-or1k-tests.sh

cd $HOME/src/tools

cd /src

function run_test {
    export JOB=$1
    export SIM=$2
    export PIPELINE=$3
    export EXPECTED_FAILURES=$4
    export EXTRA_CORE_ARGS=$5

    echo "Running Job $1 $2 $3"

    ./.travis/run-${JOB}.sh
}

run_test verilator
run_test or1k-tests icarus CAPPUCCINO
run_test or1k-tests icarus CAPPUCCINO "or1k-cy"
run_test or1k-tests icarus CAPPUCCINO "or1k-cy" "--feature_dmmu NONE"
run_test or1k-tests icarus CAPPUCCINO "or1k-cy or1k-dsxinsn" "--feature_immu NONE"
run_test or1k-tests icarus CAPPUCCINO "or1k-cy" "--feature_datacache NONE"
run_test or1k-tests icarus CAPPUCCINO "or1k-cy" "--feature_instructioncache NONE"
run_test or1k-tests icarus CAPPUCCINO "or1k-cy" "--feature_debugunit NONE"
run_test or1k-tests icarus CAPPUCCINO "or1k-cy or1k-cmov" "--feature_cmov NONE"
run_test or1k-tests icarus CAPPUCCINO "or1k-cy or1k-ext" "--feature_ext NONE"
run_test or1k-tests icarus ESPRESSO 
