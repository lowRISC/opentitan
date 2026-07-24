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

# We will lose serial access when we reboot, but if tests fail we should reboot
# in case we've crashed the UART handler on the CW340's SAM3U
# Note that the hyperdebug backend does not have the reset-sam3x command so this will fail but not trigger an error.
trap './bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface=${fpga} fpga reset-sam3x || true' EXIT

# FIXME: #16543 The following step sometimes has trouble reading the I2C we'll
# log it better and continue even if it fails (the pll is mostly correctly set
# anyway).
# Note that the hyperdebug backend does not have the set-pll command so this will fail but not trigger an error.
./bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface="$fpga" --logging debug fpga set-pll || true

# Clear the bitstream once before the whole batch starts, in case a previous
# job left the FPGA in a bad or wedged state.
./bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface="$fpga" fpga clear-bitstream

# Print the SAM3X firmware version. HyperDebug transports don't currently support this, so we ignore errors.
./bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface="$fpga" fpga get-sam3x-fw-version || true

# Run a minimal, dedicated test before the rest of the batch. Its setup already loads the
# bitstream and preloads the ROM/OTP like any other FPGA test.
./bazelisk.sh test \
    --define DISABLE_VERILATOR_BUILD=true \
    --define "$fpga"=lowrisc \
    --test_output=all \
    //sw/device/tests:fpga_priming_test_fpga_cw340_sival "$@"

./bazelisk.sh test \
    --run_under=//ci/scripts:run_test \
    --define DISABLE_VERILATOR_BUILD=true \
    --nokeep_going \
    --test_output=all \
    --build_tests_only \
    --define "$fpga"=lowrisc \
    --flaky_test_attempts=2 \
    --target_pattern_file="${target_pattern_file}" "$@"
