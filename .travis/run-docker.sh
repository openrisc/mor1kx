#!/bin/sh
# Used in travis to kick of docker

docker run --rm -v $(pwd):/src \
   -e JOB=$JOB \
   -e SIM=$SIM \
   -e PIPELINE=$PIPELINE \
   -e "EXPECTED_FAILURES=$EXPECTED_FAILURES" \
   -e "EXTRA_CORE_ARGS=$EXTRA_CORE_ARGS" \
  librecores/librecores-ci-openrisc /src/.travis/test.sh
