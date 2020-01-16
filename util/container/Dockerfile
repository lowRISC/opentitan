# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Docker container containing various hardware and software development tools
# for OpenTitan.

# Global configuration options.
ARG VERILATOR_VERSION=4.010

# The RISCV toolchain version should match the release tag used in GitHub.
ARG RISCV_TOOLCHAIN_TAR_VERSION=20190807-1

# Build OpenOCD
# OpenOCD is a tool to connect with the target chip over JTAG and similar
# transports.
FROM ubuntu:16.04 AS openocd
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
FROM ubuntu:16.04 as verilator
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
    http://git.veripool.org/git/verilator /usr/local/src/verilator
RUN cd /usr/local/src/verilator && \
    autoconf && ./configure --prefix=/tools/verilator/${VERILATOR_VERSION} && \
    make -j$(nproc) && make install


# Main container image.
FROM ubuntu:16.04 AS opentitan
ARG VERILATOR_VERSION
ARG RISCV_TOOLCHAIN_TAR_VERSION

LABEL version="1.0"
LABEL description="OpenTitan container for hardware development."
LABEL maintainer="miguelosorio@google.com"

# Copy tools from previous build stages
WORKDIR /tools
COPY --from=openocd /tools/openocd openocd
COPY --from=verilator /tools/verilator/${VERILATOR_VERSION} verilator/${VERILATOR_VERSION}

# Required packages
RUN apt-get update && apt-get install -y \
    build-essential \
    curl \
    git \
    gnupg2 \
    libc6-i386 \
    libelf-dev \
    libftdi-dev \
    libftdi1-dev \
    libftdi1 \
    libssl-dev \
    libtool \
    libusb-1.0-0-dev \
    libxml2-dev \
    minicom \
    ninja-build \
    pkgconf \
    screen \
    srecord \
    zlib1g-dev

# Install Python 3 and support libraries. Cleanup install in place to reduce
# binary size.
RUN apt-get install -y \
    python3 \
    python3-pip \
    python3-setuptools && \
    apt-get clean; rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* /usr/share/doc/*

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
