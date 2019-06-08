# dockerfile to simulate the travis environment only for testing purposes,
# this is not actually used in travis
#
# to use:
#   sudo docker build -t travis-mor1kx .travis/
#   sudo docker run -it --rm -v ${PWD}:/tmp/src/cores/mor1kx:Z travis-mor1kx
#   $ .travis/install-or1k-tests.sh && .travis/run-or1k-tests.sh
#
# tip:
#  If you only want to test the run-*.sh scripts and find install takes too
#  long you can add 'RUN .travis/install-or1k-tests.sh' and
#  'RUN .travis/install-verilator.sh' to this dockerfile to have an image
#  with the full environment already installed.
#
FROM librecores/librecores-ci:latest
RUN apt-get update && apt-get install -y \
 build-essential \
 autoconf \
 git \
 curl \
 python3-pip \
 libelf-dev \
 flex bison

RUN groupadd -g 999 travis && \
    useradd -m -r -u 999 -g travis travis
USER travis

RUN mkdir -p /tmp/src/cores/mor1kx
VOLUME /tmp/src/cores/mor1kx
ENV TRAVIS_BUILD_DIR=/tmp/src/cores/mor1kx
WORKDIR /tmp/src/cores/mor1kx

ENV PIPELINE=CAPPUCCINO
ENV SIM=icarus

LABEL maintainer Stafford Horne <shorne@gmail.com>
