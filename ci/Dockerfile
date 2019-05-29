# Dockerfile that uses librecores/librecores-ci-dev

FROM librecores/librecores-ci-dev:latest

COPY install-or1k-tests.sh /tmp

RUN apt-get update && apt-get install -y curl
RUN sh /tmp/install-or1k-tests.sh

