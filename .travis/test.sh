#!/bin/bash

export HOME=/tmp

# Setup fusesoc and add the cores required by or1k-tests
fusesoc init -y
fusesoc library add mor1kx-generic https://github.com/stffrdhrn/mor1kx-generic.git
fusesoc library add intgen https://github.com/stffrdhrn/intgen.git
fusesoc library add mor1kx /src

cd $HOME/src/tools

cd /src

echo "Running Job $JOB $SIM $PIPELINE"
echo "Expected failures: $EXPECTED_FAILURES"
echo "Extra core args: $EXTRA_CORE_ARGS"

./.travis/run-${JOB}.sh
