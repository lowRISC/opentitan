#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -x
set -e

. util/build_consts.sh
readonly SHA=$(git rev-parse HEAD)
readonly BIT_CACHE_DIR="${HOME}/.cache/opentitan-bitstreams/cache/${SHA}"
readonly BIT_SRC_PREFIX="${BIN_DIR}/hw/top_earlgrey/lowrisc_systems_chip_earlgrey_cw310_0.1.bit"
readonly BIT_DST_PREFIX="${BIT_CACHE_DIR}/lowrisc_systems_chip_earlgrey_cw310_0.1.bit"

mkdir -p ${BIT_CACHE_DIR}
for suffix in orig splice; do
  cp "${BIT_SRC_PREFIX}.${suffix}" "${BIT_DST_PREFIX}.${suffix}"
done
echo -n ${SHA} > ${BIT_CACHE_DIR}/../../latest.txt
export BITSTREAM="--offline --list ${SHA}"

# We will lose serial access when we reboot, but if tests fail we should reboot
# in case we've crashed the UART handler on the CW310's SAM3U
trap 'python3 ./util/fpga/cw310_reboot.py' EXIT

ci/bazelisk.sh test \
    --define DISABLE_VERILATOR_BUILD=true \
    --nokeep_going \
    --test_tag_filters=cw310,-broken \
    --test_output=all \
    --build_tests_only \
    --define cw310=lowrisc \
    $(./bazelisk.sh query 'rdeps(//...,@bitstreams//:bitstream_test_rom)') \
    $(./bazelisk.sh query 'rdeps(//...,@bitstreams//:bitstream_mask_rom)')
