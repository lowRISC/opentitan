#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -x
set -e

. util/build_consts.sh

SHA=$(git rev-parse HEAD)
readonly SHA

if [ $# == 0 ]; then
    echo >&2 "Usage: run-fpga-tests.sh <fpga> <tags>"
    echo >&2 "E.g. ./run-fpga-tests.sh cw310 cw310_rom"
    echo >&2 "E.g. ./run-fpga-tests.sh cw340 cw340_rom cw340_test_rom"
    exit 1
fi
fpga="$1"
shift
fpga_tags=("$@")

# Copy bitstreams and related files into the cache directory so Bazel will have
# the corresponding targets in the @bitstreams workspace.
readonly BIT_CACHE_DIR="${HOME}/.cache/opentitan-bitstreams/cache/${SHA}"
if [ "${fpga}" = "hyper310" ]; then
    readonly BIT_SRC_DIR="${BIN_DIR}/hw/top_earlgrey/chip_earlgrey_cw310_hyperdebug"
else
    readonly BIT_SRC_DIR="${BIN_DIR}/hw/top_earlgrey/chip_earlgrey_${fpga}"
fi
mkdir -p "${BIT_CACHE_DIR}"
cp -rt "${BIT_CACHE_DIR}" "${BIT_SRC_DIR}"/*

echo -n "$SHA" > "${BIT_CACHE_DIR}/../../latest.txt"
export BITSTREAM="--offline --list ${SHA}"

# We will lose serial access when we reboot, but if tests fail we should reboot
# in case we've crashed the UART handler on the CW310's SAM3U
# Note that the hyperdebug backend does not have the reset-sam3x command so this will fail but not trigger an error.
trap 'ci/bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface=${fpga} fpga reset-sam3x || true' EXIT

# In case tests update OTP or otherwise leave state on the FPGA we should start
# by clearing the bitstream.
# FIXME: #16543 The following step sometimes has trouble reading the I2C we'll
# log it better and continue even if it fails (the pll is mostly correctly set
# anyway).
# Note that the hyperdebug backend does not have the set-pll command so this will fail but not trigger an error.
ci/bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface="$fpga" --logging debug fpga set-pll || true
ci/bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface="$fpga" fpga clear-bitstream

for tag in "${fpga_tags[@]}"; do
    ci/bazelisk.sh test //... @manufacturer_test_hooks//...\
        --define DISABLE_VERILATOR_BUILD=true \
        --nokeep_going \
        --test_tag_filters="${tag}",-broken,-skip_in_ci \
        --test_timeout_filters=short,moderate \
        --test_output=all \
        --build_tests_only \
        --define "$fpga"=lowrisc \
        --flaky_test_attempts=2
done
