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
    echo >&2 "Usage: run-fpga-cw310-tests.sh <cw310_tags>"
    echo >&2 "E.g. ./run-fpga-cw310-tests.sh cw310_rom"
    echo >&2 "E.g. ./run-fpga-cw310-tests.sh cw310_rom cw310_test_rom"
    exit 1
fi
cw310_tags=("$@")

# Copy bitstreams and related files into the cache directory so Bazel will have
# the corresponding targets in the @bitstreams workspace.
#
# TODO(#13807) Update this when we change the naming scheme.
readonly BIT_CACHE_DIR="${HOME}/.cache/opentitan-bitstreams/cache/${SHA}"
readonly BIT_SRC_DIR="${BIN_DIR}/hw/top_earlgrey"
readonly BIT_NAME_PREFIX="lowrisc_systems_chip_earlgrey_cw310_0.1.bit"
mkdir -p "${BIT_CACHE_DIR}"
cp "${BIT_SRC_DIR}/${BIT_NAME_PREFIX}.orig" \
    "${BIT_SRC_DIR}/otp.mmi"  \
    "${BIT_SRC_DIR}/rom.mmi" \
    "${BIT_CACHE_DIR}"

echo -n "$SHA" > "${BIT_CACHE_DIR}/../../latest.txt"
export BITSTREAM="--offline --list ${SHA}"

# We will lose serial access when we reboot, but if tests fail we should reboot
# in case we've crashed the UART handler on the CW310's SAM3U
trap 'ci/bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface=cw310 fpga reset-sam3x' EXIT

# In case tests update OTP or otherwise leave state on the FPGA we should start
# by clearing the bitstream.
# FIXME: #16543 The following step sometimes has trouble reading the I2C we'll
# log it better and continue even if it fails (the pll is mostly correctly set
# anyway).
ci/bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface=cw310 --logging debug fpga set-pll || true
ci/bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface=cw310 fpga clear-bitstream

for tag in "${cw310_tags[@]}"; do
    ci/bazelisk.sh test //... @manufacturer_test_hooks//...\
        --define DISABLE_VERILATOR_BUILD=true \
        --nokeep_going \
        --test_tag_filters="${tag}",-broken,-skip_in_ci \
        --test_timeout_filters=short,moderate \
        --test_output=all \
        --build_tests_only \
        --define cw310=lowrisc \
        --flaky_test_attempts=2

done
