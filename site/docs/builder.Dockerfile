# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu:18.04

RUN apt-get update && \
  apt-get install -y locales locales-all git curl doxygen python3 python3-pip xsltproc && \
  apt-get clean; rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* /usr/share/doc/*

ENV LC_ALL en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en

COPY python-requirements.txt ./
RUN pip3 install -r python-requirements.txt
