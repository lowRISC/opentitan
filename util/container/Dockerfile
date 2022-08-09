# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Docker container containing various hardware and software development tools
# for OpenTitan.

# Global configuration options.
ARG VERILATOR_VERSION=4.210
ARG OPENOCD_VERSION=0.11.0
ARG VERIBLE_VERSION=v0.0-2135-gb534c1fe
# The RISCV toolchain version should match the release tag used in GitHub.
ARG RISCV_TOOLCHAIN_TAR_VERSION=20220210-1
ARG RUST_VERSION=1.60.0
# This should match the version in bazelish.sh.
ARG BAZELISK_VERSION=v1.11.0
# This should match the version in ci/install-package-dependencies.sh
ARG GCC_VERSION=9

# Main container image.
FROM ubuntu:18.04 AS opentitan
ARG VERILATOR_VERSION
ARG OPENOCD_VERSION
ARG VERIBLE_VERSION
ARG RISCV_TOOLCHAIN_TAR_VERSION
ARG RUST_VERSION
ARG BAZELISK_VERSION
ARG GCC_VERSION

LABEL version="1.0"
LABEL description="OpenTitan development container."
LABEL maintainer="opentitan-dev@opentitan.org"

# Use bash as default shell.
RUN ln -sf /bin/bash /bin/sh

# Add OBS repository to apt sources.
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
    mv "$TMPDIR/obs.list" /etc/apt/sources.list.d/edatools.list

# Install system packages
#
# Install (and cleanup) required packages (from apt-requirements.txt).
# Also add some additional packages for the use within this container and for
# developer convenience:
# - gosu and sudo are used by the scripting to make the image more convenient
#   to use.
# - locales and locales-all are required to set the locale.
# - minicom and screen are useful to see UART communication.
# - dc and time are requirements of Synopsys VCS.
# - software-properties-common is required to be able to install newer gcc versions.
COPY apt-requirements.txt /tmp/apt-requirements.txt
RUN echo "verilator-${VERILATOR_VERSION}" >>/tmp/apt-requirements.txt \
    && echo "openocd-${OPENOCD_VERSION}"  >>/tmp/apt-requirements.txt \
    && sed -i -e '/^$/d' -e '/^#/d' -e 's/#.*//' /tmp/apt-requirements.txt \
    && apt-get update \
    && xargs apt-get install -y </tmp/apt-requirements.txt \
    && apt-get install -y \
        sudo \
        gosu \
        locales \
        locales-all \
        minicom \
        screen \
        dc \
        time \
        software-properties-common \
    && apt-get clean; \
    rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* /usr/share/doc/*

# Install the CI version of gcc and g++
RUN add-apt-repository ppa:ubuntu-toolchain-r/test \
    && apt-get update \
    && apt-get install -y gcc-${GCC_VERSION} g++-${GCC_VERSION} \
    && update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-${GCC_VERSION} 90 \
    && update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-${GCC_VERSION} 90

# RISC-V device toolchain
COPY util/get-toolchain.py /tmp/get-toolchain.py
RUN /tmp/get-toolchain.py -r ${RISCV_TOOLCHAIN_TAR_VERSION} \
    && rm -f /tmp/get-toolchain.py

# Install Verible
RUN curl -f -Ls -o verible.tar.gz \
        https://github.com/chipsalliance/verible/releases/download/${VERIBLE_VERSION}/verible-${VERIBLE_VERSION}-Ubuntu-18.04-bionic-x86_64.tar.gz \
    && mkdir -p /tools/verible \
    && tar -C /tools/verible -xf verible.tar.gz --strip-components=1
ENV PATH "/tools/verible/bin:${PATH}"

# Set Locale to utf-8 everywhere
ENV LC_ALL en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en

# Scripting for use within this container.
COPY util/container/start.sh /start.sh
COPY util/container/sudoconf /etc/sudoers.d/dev

# Add the development user (UID/GID to be replaced).
RUN groupadd dev \
    && useradd --create-home -g dev dev \
    && usermod -p '*' dev \
    && passwd -u dev

# All subsequent steps are performed as user.
USER dev:dev

# Install Rust plus packages.
COPY --chown=dev:dev sw/vendor/rustup/rustup-init.sh /tmp/rustup-init.sh
RUN /tmp/rustup-init.sh -y --default-toolchain ${RUST_VERSION} \
    && rm -f /tmp/rustup-init.sh

# Install Python plus packages.
#
# Explicitly updating pip and setuptools is required to have these tools
# properly parse Python-version metadata, which some packages uses to
# specify that an older version of a package must be used for a certain
# Python version. If that information is not read, pip installs the latest
# version, which then fails to run.
ENV PATH "/home/dev/.local/bin:${PATH}"
COPY --chown=dev:dev python-requirements.txt /tmp/python-requirements.txt
RUN python3 -m pip install --user -U pip setuptools \
    && python3 -m pip install --user -r /tmp/python-requirements.txt \
        --no-warn-script-location \
    && rm -f /tmp/python-requirements.txt

USER root:root

# Install bazel using bazelisk.
RUN BAZELISK_PATH="/usr/local/bin/bazelisk"; \
    BAZELISK_URL="https://github.com/bazelbuild/bazelisk/releases/download/${BAZELISK_VERSION}/bazelisk-linux-amd64"; \
    curl -L -o ${BAZELISK_PATH} ${BAZELISK_URL} && \
    chmod +x ${BAZELISK_PATH} && \
    ln -s ${BAZELISK_PATH} /usr/local/bin/bazel

RUN runuser dev -c "bazel > /dev/null"

ENTRYPOINT [ "/start.sh" ]
