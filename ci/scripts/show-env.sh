#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A script that dumps the current environment, plus the versions of
# various tools to stdout.

set -e

required_tools=(
    git
    python3
    yapf
    isort
    flake8
    ninja
    doxygen
)

optional_tools=(
    verible-verilog-lint
)

for tool in "${required_tools[@]}"; do
    set -x
    $tool --version
    { set +x; } 2>/dev/null
    echo
done

for tool in "${optional_tools[@]}"; do
    set -x
    $tool --version || echo "Warning: failed to determine version of $tool"
    { set +x; } 2>/dev/null
    echo
done

set -x
echo "PATH=$PATH"
{ set +x; } 2>/dev/null
echo

set -x
printenv
