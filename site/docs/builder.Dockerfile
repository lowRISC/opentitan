# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu:18.04

RUN apt-get update && apt-get install -y git curl python3 python3-pip && \
  apt-get clean; rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* /usr/share/doc/*
COPY python-requirements.txt ./
RUN pip3 install -r python-requirements.txt
