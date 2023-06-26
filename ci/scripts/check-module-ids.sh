#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Checks that all status_t module IDs are unique.

set -e

# List of all targets that need to be checked: we only consider targets that
# produce a binary file and that depend on the status library. Since every test
# is usually built for FPGA and simulation targets, we only check for one target to
# save time.
query_elfs='
    filter(
        ".*fpga_cw310.*",
        kind(
            cc_binary,
            rdeps(
                //sw/device/...,
                //sw/device/lib/base:status
            )
        )
    )'
target_file=$(mktemp)
./bazelisk.sh query "$query_elfs" >"$target_file"
# We now ask bazel to build all targets but we also add the module ID checker aspect
# and we query the corresponding output group to force bazel to run the checks.
./ci/bazelisk.sh build \
    --config=riscv32 \
    --aspects=rules/quality.bzl%modid_check_aspect \
    --output_groups=modid_check \
    --target_pattern_file="$target_file"
