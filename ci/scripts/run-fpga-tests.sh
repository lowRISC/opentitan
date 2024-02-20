#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -x
set -e

. util/build_consts.sh

if [ $# == 0 ]; then
    echo >&2 "Usage: run-fpga-tests.sh <fpga> <tags or test set name>"
    echo >&2 "E.g. ./run-fpga-tests.sh cw310 manuf"
    echo >&2 "E.g. ./run-fpga-tests.sh cw310 cw310_rom_tests"
    exit 1
fi
fpga="$1"
fpga_tags="$2"

# Copy bitstreams and related files into the cache directory so Bazel will have
# the corresponding targets in the @bitstreams workspace.
readonly BIT_CACHE_DIR="${HOME}/.cache/opentitan-bitstreams/cache/ci_bitstreams"
if [ "${fpga}" = "hyper310" ]; then
    readonly BIT_SRC_DIR="${BIN_DIR}/hw/top_earlgrey/chip_earlgrey_cw310_hyperdebug"
else
    readonly BIT_SRC_DIR="${BIN_DIR}/hw/top_earlgrey/chip_earlgrey_${fpga}"
fi
mkdir -p "${BIT_CACHE_DIR}"
cp -rt "${BIT_CACHE_DIR}" "${BIT_SRC_DIR}"/*

export BITSTREAM="--offline --list ci_bitstreams"

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

pattern_file=$(mktemp)
# Recognize special test set names, otherwise we interpret it as a list of tags.
test_args=""
echo "tags: ${fpga_tags}"
if [ "${fpga_tags}" == "cw310_sival_but_not_rom_ext_tests" ]
then
    # Only consider tests that are tagged `cw310_sival` but not tagged `cw310_sival_rom_ext`.
    # The difficulty is that, technically, they are different tests since `opentitan_test` creates
    # one target for each execution environment. The following query relies on the existence
    # of the test suite created by `opentitan_test` that depends on all per-exec-env tests.
    ci/bazelisk.sh query \
    "
        `# Find all test tagged cw310_sival that are dependencies of the test suite identified`
        attr(
            \"tags\",
            \"cw310_sival([^_]|$)\",
            deps(
                `# Find all test suites depending on a test tagged cw310_sival` \
                kind(
                    \"test_suite\",
                    rdeps(
                        //...,
                        `# Find all tests tagged cw310_sival`
                        attr(\"tags\",\"cw310_sival([^_]|$)\", //...),
                        1
                    )
                )
                except
                `# Remove all test suites depending on a test tagged cw310_sival_rom_ext`
                rdeps(
                    //...,
                    `# Find all tests tagged cw310_sival_rom_ext`
                    attr(\"tags\",\"cw310_sival_rom_ext\", //...),
                    1
                ),
                1
            )
        )
    " \
    > "${pattern_file}"
    test_args="${test_args} --test_tag_filters=-broken,-skip_in_ci"
else
    test_args="${test_args} --test_tag_filters=${fpga_tags},-broken,-skip_in_ci"
    echo "//..." > "${pattern_file}"
    echo "@manufacturer_test_hooks//..." >> "${pattern_file}"
fi

ci/bazelisk.sh test \
    --define DISABLE_VERILATOR_BUILD=true \
    --nokeep_going \
    --test_timeout_filters=short,moderate \
    --test_output=all \
    --build_tests_only \
    --define "$fpga"=lowrisc \
    --flaky_test_attempts=2 \
    --target_pattern_file="${pattern_file}" \
    ${test_args}
