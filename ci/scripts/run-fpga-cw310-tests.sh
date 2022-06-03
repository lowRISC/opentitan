#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -x
set -e

. util/build_consts.sh
SHA=$(git rev-parse HEAD)
BITCACHE_DIR=~/.cache/opentitan-bitstreams/cache/${SHA}
mkdir -p $BITCACHE_DIR
BITCACHE_FILE=$BITCACHE_DIR/lowrisc_systems_chip_earlgrey_cw310_0.1.bit.orig
cp $BIN_DIR/hw/top_earlgrey/lowrisc_systems_chip_earlgrey_cw310_0.1.bit ${BITCACHE_FILE}
echo "" >> ${BITCACHE_DIR}/lowrisc_systems_chip_earlgrey_cw310_0.1.bit.splice
echo -n ${SHA} > ${BITCACHE_DIR}/../../latest.txt
export BITSTREAM="--offline --list ${SHA}"

# TODO: remove the --notest_keep_going and --nokeep_going flag after the CW310
# tests are reliable (#13044)
ci/bazelisk.sh test \
    --define DISABLE_VERILATOR_BUILD=true \
    --notest_keep_going \
    --nokeep_going \
    --test_tag_filters=cw310,-broken \
    --test_output=all \
    --build_tests_only \
    --define cw310=lowrisc \
    //sw/device/tests:otbn_randomness_test_fpga_cw310 \
    //sw/device/tests:kmac_mode_cshake_test_fpga_cw310 \
    //sw/device/tests:kmac_mode_kmac_test_fpga_cw310 \
    //sw/device/silicon_creator/lib/drivers:hmac_functest_fpga_cw310 \
    //sw/device/silicon_creator/lib/drivers:uart_functest_fpga_cw310 \
    //sw/device/silicon_creator/lib/drivers:retention_sram_functest_fpga_cw310
    # //sw/device/tests:pmp_smoketest_napot_fpga_cw310 \
    # //sw/device/tests:pmp_smoketest_tor_fpga_cw310 \
    # Note that the pmp_smoketest_* tests were included in the original
    # systemtest but are failing when run under bazel and so are excluded from
    # this run
    # TODO: use the following query instead of the list above after the CW310
    # UART is reliable (#13044)
    # $(./bazelisk.sh query 'rdeps(//...,@bitstreams//:bitstream_test_rom)') \
    # All the tests that depend on the test rom
