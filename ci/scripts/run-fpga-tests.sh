#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -x
set -e

. util/build_consts.sh

if [ $# == 0 ]; then
    echo >&2 "Usage: run-fpga-tests.sh <fpga> <target_pattern_file> [bazel options...]"
    echo >&2 "E.g. ./run-fpga-tests.sh cw340 list_of_test.txt --cache_test_results=no"
    exit 1
fi
fpga="$1"
target_pattern_file="$2"
shift 2

# Copy bitstreams and related files into the cache directory so Bazel will have
# the corresponding targets in the @bitstreams workspace.
readonly BIT_CACHE_DIR="${HOME}/.cache/opentitan-bitstreams/cache/ci_bitstreams"
readonly BIT_SRC_DIR="${BIN_DIR}/hw/top_earlgrey/chip_earlgrey_${fpga}"
mkdir -p "${BIT_CACHE_DIR}"
cp -rt "${BIT_CACHE_DIR}" "${BIT_SRC_DIR}"/*

export BITSTREAM="--offline --list ci_bitstreams"

# Make sure that the SAM3x is in a good state.
# We first power cycle the hub port to make sure that we can talk the device (its USB handler
# seems to get stuck sometimes), and then gently ask it to reboot.
./bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface=${fpga} fpga reset-sam3x --power-cycle || true
./bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface=${fpga} fpga reset-sam3x || true

# Running tests will clear all non-volatile memory on the FPGA, but we start by
# clearing the bitstream to be cautious in case tests leave behind some state.
# FIXME: #16543 The following step sometimes has trouble reading the I2C we'll
# log it better and continue even if it fails (the pll is mostly correctly set
# anyway).
# Note that the hyperdebug backend does not have the set-pll command so this will fail but not trigger an error.
./bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface="$fpga" --logging debug fpga set-pll || true
./bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface="$fpga" fpga clear-bitstream

# Print the SAM3X firmware version. HyperDebug transports don't currently support this, so we ignore errors.
./bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface="$fpga" fpga get-sam3x-fw-version || true

./bazelisk.sh test \
    --run_under=//ci/scripts:run_test \
    --define DISABLE_VERILATOR_BUILD=true \
    --nokeep_going \
    --test_output=all \
    --build_tests_only \
    --define "$fpga"=lowrisc \
    --flaky_test_attempts=2 \
    --target_pattern_file="${target_pattern_file}" "$@"
