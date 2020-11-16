# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Docker container containing various hardware and software development tools
# for OpenTitan.

# Global configuration options.
ARG VERILATOR_VERSION=4.104

# The RISCV toolchain version should match the release tag used in GitHub.
ARG RISCV_TOOLCHAIN_TAR_VERSION=20200904-1

# Build OpenOCD
# OpenOCD is a tool to connect with the target chip over JTAG and similar
# transports.
FROM ubuntu:18.04 AS openocd
RUN apt-get update && apt-get install -y \
    autoconf \
    git \
    libftdi1-dev \
    libtool \
    libusb-1.0.0-dev \
    pkg-config \
    texinfo
RUN git clone --depth=1 https://github.com/riscv/riscv-openocd.git /usr/local/src/openocd
RUN cd /usr/local/src/openocd && ./bootstrap && mkdir build && cd build && \
    ../configure --enable-ftdi --enable-verbose-jtag-io --disable-vsllink \
    --enable-remote-bitbang --prefix=/tools/openocd && \
    make -j$(nproc) && make install

# Build Verilator.
FROM ubuntu:18.04 as verilator
ARG VERILATOR_VERSION
RUN apt-get update && apt-get install -y \
    autoconf \
    automake \
    autotools-dev \
    bison \
    build-essential \
    flex \
    git
RUN git clone --depth=1 -b  v${VERILATOR_VERSION} \
    https://github.com/verilator/verilator.git /usr/local/src/verilator
RUN cd /usr/local/src/verilator && \
    autoconf && ./configure --prefix=/tools/verilator/${VERILATOR_VERSION} && \
    make -j$(nproc) && make install


# Main container image.
FROM ubuntu:18.04 AS opentitan
ARG VERILATOR_VERSION
ARG RISCV_TOOLCHAIN_TAR_VERSION

LABEL version="1.0"
LABEL description="OpenTitan container for hardware development."
LABEL maintainer="miguelosorio@google.com"

# Copy tools from previous build stages
WORKDIR /tools
COPY --from=openocd /tools/openocd openocd
COPY --from=verilator /tools/verilator/${VERILATOR_VERSION} verilator/${VERILATOR_VERSION}

# Install (and cleanup) required packages (from apt-requirements.txt)
# The list of extra packages is leftover from before this Dockerfile used
# apt-requirements.txt
#
# This also adds `locales` and `locales-all` so we can set the locale to utf-8
COPY apt-requirements.txt /tmp/apt-requirements.txt
RUN apt-get update && \
    sed 's/#.*//' /tmp/apt-requirements.txt \
        | xargs apt-get install -y && \
    apt-get install -y \
        locales \
        locales-all \
        gnupg2 \
        libc6-i386 \
        libtool \
        minicom \
        screen && \
    apt-get clean ; \
    rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* /usr/share/doc/*

# Set Locale to utf-8 everywhere
ENV LC_ALL en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en

# Copy repository into tmp directory to execute additional install steps.
COPY python-requirements.txt /tmp/python-requirements.txt
RUN pip3 install -r /tmp/python-requirements.txt

COPY util/get-toolchain.py /tmp/get-toolchain.py
RUN /tmp/get-toolchain.py -r ${RISCV_TOOLCHAIN_TAR_VERSION}
RUN rm /tmp/python-requirements.txt /tmp/get-toolchain.py

# Use bash as default shell
RUN ln -sf /bin/bash /bin/sh

# Include tools in PATH.
ENV PATH "/tools/verilator/${VERILATOR_VERSION}/bin:${PATH}"

# Configures default container user.
ENV USER ot

ENTRYPOINT /bin/bash
