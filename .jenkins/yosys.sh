#! /bin/bash

# yosys.sh script can be run on local instance with command : 
# docker run --rm -v $(pwd):/src librecores/librecores-ci:0.4.0 /src/.jenkins/yosys.sh 
# It will produce 'Printing Statistics' for monitoring resource usages by running yosys synthesis
cd /src

fusesoc library add mor1kx /src
fusesoc run --target=synth mor1kx
/test-scripts/extract-yosys-stats.py  < build/mor1kx_5.0-r3/synth-icestorm/yosys.log