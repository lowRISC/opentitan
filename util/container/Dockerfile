# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Docker container containing various hardware and software development tools
# for OpenTitan.

# Global configuration options.
ARG VERILATOR_VERSION=4.104
ARG OPENOCD_VERSION=0.11.0

# The RISCV toolchain version should match the release tag used in GitHub.
ARG RISCV_TOOLCHAIN_TAR_VERSION=20210412-1

# Main container image.
FROM ubuntu:18.04 AS opentitan
ARG VERILATOR_VERSION
ARG OPENOCD_VERSION
ARG RISCV_TOOLCHAIN_TAR_VERSION

LABEL version="1.0"
LABEL description="OpenTitan container for hardware development."
LABEL maintainer="miguelosorio@google.com"

WORKDIR /tools

# Add OBS repository to apt sources
RUN OBS_URL="https://download.opensuse.org/repositories"; \
    OBS_PATH="/home:/phiwag:/edatools/xUbuntu_18.04"; \
    REPO_URL="${OBS_URL}${OBS_PATH}"; \
    \
    EDATOOLS_REPO_KEY="${REPO_URL}/Release.key"; \
    EDATOOLS_REPO="deb ${REPO_URL}/ /"; \
    \
    apt-get update && \
    apt-get install -y curl && \
    \
    curl -f -sL -o "$TMPDIR/obs.asc" "$EDATOOLS_REPO_KEY" || { \
        error "Failed to download repository key from ${REPO_URL}"; \
    } && \
    echo "$EDATOOLS_REPO" > "$TMPDIR/obs.list" && \
    mv "$TMPDIR/obs.asc"  /etc/apt/trusted.gpg.d/obs.asc && \
    mv "$TMPDIR/obs.list" /etc/apt/sources.list.d/edatools.list && \
    apt-get update

# Install (and cleanup) required packages (from apt-requirements.txt)
# The list of extra packages is leftover from before this Dockerfile used
# apt-requirements.txt
#
# This also adds `locales` and `locales-all` so we can set the locale to utf-8
COPY apt-requirements.txt /tmp/apt-requirements.txt
RUN echo "verilator-${VERILATOR_VERSION}" >>/tmp/apt-requirements.txt && \
    echo "openocd-${OPENOCD_VERSION}"     >>/tmp/apt-requirements.txt && \
    sed -i -e '/^$/d' -e '/^#/d' -e 's/#.*//' /tmp/apt-requirements.txt && \
    xargs apt-get install -y </tmp/apt-requirements.txt && \
    apt-get update && apt-get install -y \
        locales \
        locales-all \
        gnupg2 \
        libc6-i386 \
        libtool \
        minicom \
        screen && \
    apt-get clean; \
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
