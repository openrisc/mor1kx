# dockerfile to simulate the ci environment only for testing purposes,
# this is not actually used in ci
#
# to use:
#   podman build -t mor1kx-ci .github/workflows/
#   podman run -it --rm -v ${PWD}:/tmp/src/cores/mor1kx:Z mor1kx-ci
#   $ # run stuff from ci.yml
#
# tip:
#  If you only want to test the run-*.sh scripts and find install takes too
#  long you can add 'RUN .travis/install-or1k-tests.sh' and
#  'RUN .travis/install-verilator.sh' to this dockerfile to have an image
#  with the full environment already installed.
#
FROM ubuntu:24.04
RUN apt-get update && apt-get -y install build-essential python3 python3-pip python3.12-venv xz-utils git iverilog \
  libfl2 libelf-dev

RUN python3 -m venv /tmp/fusesoc_venv
ENV PATH="/tmp/fusesoc_venv/bin:$PATH"
RUN pip3 install fusesoc

#RUN pip3 install --upgrade setuptools wheel
#RUN pip3 install --upgrade fusesoc

RUN apt-get -y install curl

RUN groupadd -g 999 runner && \
    useradd -m -r -u 999 -g runner runner
#USER runner

RUN mkdir -p /tmp/src/cores/mor1kx
VOLUME /tmp/src/cores/mor1kx
WORKDIR /tmp/src/cores/mor1kx

LABEL maintainer Stafford Horne <shorne@gmail.com>
