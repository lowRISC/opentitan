# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Docker container containing various hardware and software development tools
# for OpenTitan, based on the Claude Code sandbox image.
#
# Build from $REPO_TOP:
#   docker build -t opentitan-claude -f util/container/Dockerfile .

# =============================================================================
# Global configuration options
# =============================================================================
ARG VERILATOR_VERSION=4.210
ARG VERIBLE_VERSION=v0.0-3622-g07b310a3
# The RISCV toolchain version should match the release tag used in GitHub.
ARG RISCV_TOOLCHAIN_TAR_VERSION=20220210-1
# This should match the version in bazelish.sh.
ARG BAZELISK_VERSION=v1.24.1
# This should match the version of the lowRISC RISC-V toolchain.
ARG CLANG_VERSION=16

# Open-source FPGA toolchain versions for CW310 (Kintex-7 XC7K410T) bitstream
# generation without Vivado. See PLAN_opensource_cw310_bitstream.md for details.
ARG YOSYS_VERSION=yosys-0.46
ARG SV2V_VERSION=v0.0.13
ARG NEXTPNR_XILINX_VERSION=0.8.2
ARG OPENFPGALOADER_VERSION=v0.12.2

# =============================================================================
# Base image: Claude Code sandbox
# =============================================================================
# Provides: Ubuntu base, agent user with sudo, Docker CLI, Node.js, Go,
# Python 3, Git, ripgrep, jq, GitHub CLI.
FROM docker/sandbox-templates:claude-code

ARG VERILATOR_VERSION
ARG VERIBLE_VERSION
ARG RISCV_TOOLCHAIN_TAR_VERSION
ARG BAZELISK_VERSION
ARG CLANG_VERSION
ARG YOSYS_VERSION
ARG SV2V_VERSION
ARG NEXTPNR_XILINX_VERSION
ARG OPENFPGALOADER_VERSION

LABEL version="1.0"
LABEL description="OpenTitan development container with Claude Code and open-source FPGA toolchain."
LABEL maintainer="opentitan-dev@opentitan.org"

USER root

# Use bash as default shell.
RUN ln -sf /bin/bash /bin/sh

# =============================================================================
# System packages
# =============================================================================
# Necessary to avoid user interaction with tzdata during install
ARG DEBIAN_FRONTEND=noninteractive
ENV TZ=UTC

# Install OpenTitan apt requirements + sandbox development extras.
#
# Packages from apt-requirements.txt provide the OpenTitan base dependencies.
# Additional packages provide developer convenience tools for the container:
# - gosu and sudo are used by the scripting to make the image more convenient
#   to use.
# - locales and locales-all are required to set the locale.
# - minicom and screen are useful to see UART communication.
# - dc and time are requirements of Synopsys VCS.
# - software-properties-common is required to be able to install newer gcc versions.
# - Sandbox extras: tmux, htop, vim, nano, strace, net-tools, xvfb, etc.
COPY apt-requirements.txt /tmp/apt-requirements.txt
RUN sed -i -e '/^$/d' -e '/^#/d' -e 's/#.*//' /tmp/apt-requirements.txt \
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
        wget \
        vim \
        nano \
        tmux \
        htop \
        less \
        strace \
        gzip \
        net-tools \
        iputils-ping \
        openssh-client \
        coreutils \
        xvfb \
        libfontconfig1 \
        libsdl2-2.0-0 \
        python3-numpy \
        python3-opencv \
    && apt-get clean; \
    rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* /usr/share/doc/*

# =============================================================================
# Clang / LLVM toolchain (version-pinned for OpenTitan)
# =============================================================================
# Install and configure clang and llvm tools for coverage measurements.
# Note: Some commands listed below are missing in 13.0.1 and cause warnings during
# build. These are kept intentionally since we plan to use them in the future, e.g.
# `llvm-remark-size-diff` and `llvm-tli-checker`.
RUN curl https://apt.llvm.org/llvm-snapshot.gpg.key | apt-key add \
    && add-apt-repository "deb https://apt.llvm.org/jammy/ llvm-toolchain-jammy-${CLANG_VERSION} main" \
    && apt update \
    && apt install -y clang-${CLANG_VERSION} lldb-${CLANG_VERSION} lld-${CLANG_VERSION} \
        clangd-${CLANG_VERSION} clang-tidy-${CLANG_VERSION} clang-format-${CLANG_VERSION} \
        clang-tools-${CLANG_VERSION} llvm-${CLANG_VERSION} lld-${CLANG_VERSION} \
        llvm-${CLANG_VERSION}-tools \
    && ( \
        primary="llvm-config"; \
        secondary="llvm-addr2line llvm-ar llvm-as llvm-bcanalyzer llvm-bitcode-strip \
            llvm-cat llvm-cfi-verify llvm-cov llvm-c-test llvm-cvtres llvm-cxxdump llvm-cxxfilt \
            llvm-cxxmap llvm-debuginfod llvm-debuginfod-find llvm-diff llvm-dis llvm-dlltool \
            llvm-dwarfdump llvm-dwarfutil llvm-dwp llvm-exegesis llvm-extract llvm-gsymutil llvm-ifs \
            llvm-install-name-tool llvm-jitlink llvm-jitlink-executor llvm-lib llvm-libtool-darwin \
            llvm-link llvm-lipo llvm-lto llvm-lto2 llvm-mc llvm-mca llvm-ml llvm-modextract llvm-mt \
            llvm-nm llvm-objcopy llvm-objdump llvm-omp-device-info llvm-opt-report llvm-otool \
            llvm-pdbutil llvm-PerfectShuffle llvm-profdata llvm-profgen llvm-ranlib llvm-rc \
            llvm-readelf llvm-readobj llvm-reduce llvm-remark-size-diff llvm-rtdyld llvm-sim \
            llvm-size llvm-split llvm-stress llvm-strings llvm-strip llvm-symbolizer llvm-tapi-diff \
            llvm-tblgen llvm-tli-checker llvm-undname llvm-windres llvm-xray"; \
        cmd="update-alternatives --verbose --install /usr/bin/${primary} ${primary} /usr/bin/${primary}-${CLANG_VERSION} 90";\
        for s in ${secondary}; do \
            cmd="${cmd} --slave /usr/bin/${s} ${s} /usr/bin/${s}-${CLANG_VERSION}"; \
        done; \
        ${cmd} ; \
        primary="clang"; \
        secondary="analyze-build asan_symbolize bugpoint c-index-test clang++ \
            clang-apply-replacements clang-change-namespace clang-check clang-cl clang-cpp clangd \
            clang-doc clang-extdef-mapping clang-format clang-format-diff clang-include-fixer \
            clang-linker-wrapper clang-move clang-nvlink-wrapper clang-offload-bundler \
            clang-offload-packager clang-offload-wrapper clang-pseudo clang-query clang-refactor \
            clang-rename clang-reorder-fields clang-repl clang-scan-deps clang-tidy count diagtool \
            dsymutil FileCheck find-all-symbols git-clang-format hmaptool hwasan_symbolize \
            intercept-build ld64.lld ld.lld llc lld lldb lldb-argdumper lldb-instr lldb-server \
            lldb-vscode lld-link lli lli-child-target modularize not obj2yaml opt pp-trace \
            run-clang-tidy sancov sanstats scan-build scan-build-py scan-view split-file \
            UnicodeNameMappingGenerator verify-uselistorder wasm-ld yaml2obj yaml-bench"; \
        cmd="update-alternatives --verbose --install /usr/bin/${primary} ${primary} /usr/bin/${primary}-${CLANG_VERSION} 90";\
        for s in ${secondary}; do \
            cmd="${cmd} --slave /usr/bin/${s} ${s} /usr/bin/${s}-${CLANG_VERSION}"; \
        done; \
        ${cmd} ; \
    )

# =============================================================================
# HDL development tools (Verilator, Verible)
# =============================================================================

# Install verilator prebuild binary
RUN mkdir -p /tools/verilator \
    && curl -sSfL https://storage.googleapis.com/verilator-builds/verilator-v${VERILATOR_VERSION}.tar.gz | tar -C /tools/verilator -xvzf -
ENV PATH="/tools/verilator/v${VERILATOR_VERSION}/bin:${PATH}"

# Install Verible
RUN curl -f -Ls -o verible.tar.gz \
        https://github.com/chipsalliance/verible/releases/download/${VERIBLE_VERSION}/verible-${VERIBLE_VERSION}-linux-static-x86_64.tar.gz \
    && mkdir -p /tools/verible \
    && tar -C /tools/verible -xf verible.tar.gz --strip-components=1
ENV PATH="/tools/verible/bin:${PATH}"

# =============================================================================
# Open-source FPGA toolchain
# =============================================================================
# These tools enable building bitstreams for the CW310 (Kintex-7 XC7K410T)
# without Vivado, using the Yosys + nextpnr-xilinx + Project X-Ray flow.
# See PLAN_opensource_cw310_bitstream.md for the full usage guide.

# Install additional build dependencies for the open-source FPGA tools.
# Many base deps (cmake, build-essential, git, python3, libftdi1-dev, etc.)
# are already present from apt-requirements.txt.
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        tcl-dev \
        libreadline-dev \
        libffi-dev \
        libboost-system-dev \
        libboost-filesystem-dev \
        libboost-thread-dev \
        libboost-program-options-dev \
        libboost-iostreams-dev \
        libboost-dev \
        libeigen3-dev \
        gawk \
        python3-yaml \
        libhidapi-dev \
        pypy3 \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

# Install Yosys (open-source synthesis)
# Supports Xilinx 7-series via: synth_xilinx -family xc7
RUN git clone --depth 1 --branch ${YOSYS_VERSION} \
        https://github.com/YosysHQ/yosys.git /tmp/yosys \
    && cd /tmp/yosys \
    && make config-gcc \
    && make -j$(nproc) PREFIX=/tools/yosys \
    && make install PREFIX=/tools/yosys \
    && rm -rf /tmp/yosys
ENV PATH="/tools/yosys/bin:${PATH}"

# Install sv2v (SystemVerilog to Verilog converter)
# Used to preprocess OpenTitan's SystemVerilog into Verilog that Yosys can
# consume natively, bypassing SV frontend limitations.
RUN curl -sSfL -o /tmp/sv2v.tgz \
        https://github.com/zachjs/sv2v/releases/download/${SV2V_VERSION}/sv2v-Linux.tar.gz \
    && mkdir -p /tools/sv2v/bin \
    && tar -C /tools/sv2v -xzf /tmp/sv2v.tgz --strip-components=1 \
    && rm /tmp/sv2v.tgz
ENV PATH="/tools/sv2v/bin:${PATH}"

# Install Project X-Ray: bitstream tools + database for Xilinx 7-series.
# prjxray provides fasm2frames and xc7frames2bit for bitstream generation.
# prjxray-db provides the prebuilt device database (includes xc7k410t).
RUN git clone https://github.com/f4pga/prjxray.git /tools/prjxray \
    && cd /tools/prjxray \
    && git submodule update --init --recursive \
    && mkdir build && cd build \
    && cmake -DCMAKE_INSTALL_PREFIX=/tools/prjxray .. \
    && make -j$(nproc) \
    && cd .. \
    && pip3 install --break-system-packages -e . \
    && git clone https://github.com/f4pga/prjxray-db.git /tools/prjxray-db
ENV XRAY_DIR="/tools/prjxray"
ENV XRAY_DATABASE_DIR="/tools/prjxray-db"
ENV XRAY_TOOLS_DIR="/tools/prjxray/build/tools"
ENV XRAY_UTILS_DIR="/tools/prjxray/utils"
ENV PATH="/tools/prjxray/build/tools:${PATH}"

# Install nextpnr-xilinx (open-source place & route for Xilinx 7-series)
# From the openXC7 fork which adds MMCME2_ADV, BRAM, and other 7-series support.
#
# IMPORTANT: After building the container, you must generate the chip database
# for the target part before running place & route. For the CW310's XC7K410T:
#
#   cd /tools/nextpnr-xilinx/share/python
#   pypy3 bbaexport.py --device xc7k410tffg676-1 \
#       --bba /tools/nextpnr-xilinx/share/xc7k410t.bba
#   bbasm --l /tools/nextpnr-xilinx/share/xc7k410t.bba \
#       /tools/nextpnr-xilinx/share/xc7k410t.bin
#
# This requires ~16-32 GB RAM and may take 1-2 hours with pypy3.
# The resulting .bin file will be several GB.
RUN git clone --depth 1 --branch ${NEXTPNR_XILINX_VERSION} \
        https://github.com/openXC7/nextpnr-xilinx.git /tmp/nextpnr-xilinx \
    && cd /tmp/nextpnr-xilinx \
    && cmake -DARCH=xilinx -DBUILD_GUI=OFF \
        -DCMAKE_INSTALL_PREFIX=/tools/nextpnr-xilinx . \
    && make -j$(nproc) \
    && make install \
    && mkdir -p /tools/nextpnr-xilinx/share/python \
    && cp -r xilinx/python/* /tools/nextpnr-xilinx/share/python/ \
    && rm -rf /tmp/nextpnr-xilinx
ENV PATH="/tools/nextpnr-xilinx/bin:${PATH}"

# Install openFPGALoader (open-source FPGA programming via JTAG/SPI)
# Replaces Vivado Hardware Manager for loading bitstreams onto the CW310.
RUN git clone --depth 1 --branch ${OPENFPGALOADER_VERSION} \
        https://github.com/trabucayre/openFPGALoader.git /tmp/openFPGALoader \
    && cd /tmp/openFPGALoader \
    && mkdir build && cd build \
    && cmake -DCMAKE_INSTALL_PREFIX=/tools/openFPGALoader .. \
    && make -j$(nproc) \
    && make install \
    && rm -rf /tmp/openFPGALoader
ENV PATH="/tools/openFPGALoader/bin:${PATH}"

# =============================================================================
# Locale and directory setup
# =============================================================================
ENV LC_ALL=en_US.UTF-8
ENV LANG=en_US.UTF-8
ENV LANGUAGE=en_US:en

# Give the agent user access to /tools so they can install toolchains later.
RUN mkdir -p /tools \
    && chown agent:agent /tools \
    && chmod 775 /tools

# Create additional directories for projects and data.
RUN mkdir -p /workspace/projects /workspace/data

# =============================================================================
# User-space setup (agent user from sandbox base image)
# =============================================================================
USER agent

# Install Python packages required by OpenTitan.
#
# Explicitly updating pip and setuptools is required to have these tools
# properly parse Python-version metadata, which some packages uses to
# specify that an older version of a package must be used for a certain
# Python version. If that information is not read, pip installs the latest
# version, which then fails to run.
ENV PATH="/home/agent/.local/bin:${PATH}"
COPY --chown=agent:agent python-requirements.txt /tmp/python-requirements.txt
RUN python3 -m pip install --user -U pip "setuptools<66.0.0" \
    && python3 -m pip install --user -r /tmp/python-requirements.txt \
        --no-warn-script-location \
    && rm -f /tmp/python-requirements.txt

# Get the RISC-V device toolchain (installs to /tools/riscv).
COPY --chown=agent:agent util/get-toolchain.py /tmp/get-toolchain.py
RUN /tmp/get-toolchain.py -r ${RISCV_TOOLCHAIN_TAR_VERSION} \
    && rm -f /tmp/get-toolchain.py

# Claude Code configuration.
RUN echo '{"hasCompletedOnboarding": true}' > ~/.claude.json \
    && mkdir -p /home/agent/.claude \
    && echo '{"env":{"CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS":"1"},"teammateMode":"tmux"}' > /home/agent/.claude/settings.json \
    && echo 'set -g default-terminal "screen-256color"' > /home/agent/.tmux.conf

# Install .NET 8.0 runtime.
RUN curl -sSL https://dot.net/v1/dotnet-install.sh | bash /dev/stdin \
    --channel 8.0 \
    --runtime dotnet \
    --install-dir /home/agent/.dotnet

# =============================================================================
# Bazelisk (installed as root)
# =============================================================================
USER root

RUN BAZELISK_PATH="/usr/local/bin/bazelisk"; \
    BAZELISK_URL="https://github.com/bazelbuild/bazelisk/releases/download/${BAZELISK_VERSION}/bazelisk-linux-amd64"; \
    curl -L -o ${BAZELISK_PATH} ${BAZELISK_URL} && \
    chmod +x ${BAZELISK_PATH} && \
    ln -s ${BAZELISK_PATH} /usr/local/bin/bazel

RUN runuser agent -c "bazel > /dev/null"

# =============================================================================
# Final environment
# =============================================================================
ENV PATH="/home/agent/.dotnet:${PATH}"
ENV DOTNET_ROOT="/home/agent/.dotnet"
ENV PYTHONPATH="/workspace:${PYTHONPATH}"
ENV NODE_ENV=development
ENV PYTHONUNBUFFERED=1
ENV COLORTERM=truecolor
ENV ANTHROPIC_MODEL=claude-opus-4-6

WORKDIR /workspace

# The container includes:
# - Ubuntu-based environment with Claude Code
# - Docker CLI for running additional containers
# - GitHub CLI, Node.js, Go, Python 3
# - Git, ripgrep, jq
# - Non-root 'agent' user with sudo access
# - Private Docker daemon
# - OpenTitan: RISC-V toolchain, Verilator, Verible, Clang 16, Bazelisk
# - Open-source FPGA: Yosys, sv2v, nextpnr-xilinx, Project X-Ray, openFPGALoader

USER agent
CMD ["tmux", "new-session", "-s", "claude", "claude", "--dangerously-skip-permissions"]
