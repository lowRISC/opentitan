# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu:18.04

RUN apt-get update && \
    apt-get install -y \
        locales locales-all git curl doxygen python3 python3-pip xsltproc && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* /usr/share/doc/*

ENV LC_ALL en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en

COPY python-requirements.txt ./
ENV PATH "/root/.local/bin:${PATH}"
# Explicitly updating pip and setuptools is required to have these tools
# properly parse Python-version metadata, which some packages uses to
# specify that an older version of a package must be used for a certain
# Python version. If that information is not read, pip installs the latest
# version, which then fails to run.
RUN python3 -m pip install --user -U pip "setuptools<66.0.0"
RUN pip3 install --user -r python-requirements.txt
