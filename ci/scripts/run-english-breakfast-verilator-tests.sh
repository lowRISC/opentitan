#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Only a single test is supported on English Breakfast (EB).
# Currently, Bazel cannot build the EB Verilator model, so we only build the test with Bazel and then use opentitantool directly
# EB Verilator model is built in a previous CI step

set -e

. util/build_consts.sh

# Cleaning is necessary for the find commands below to work correctly
ci/bazelisk.sh clean

# Build the modified EB software.
./hw/top_englishbreakfast/util/prepare_sw.py -b

# Build some other dependencies.
ci/bazelisk.sh build  \
    --copt=-DOT_IS_ENGLISH_BREAKFAST_REDUCED_SUPPORT_FOR_INTERNAL_USE_ONLY_ \
    //sw/host/opentitantool //hw/ip/otp_ctrl/data:img_rma

# Run the one test.
# This needs to be run outside the bazel sandbox, so we do not use `bazel run`
bazel-bin/sw/host/opentitantool/opentitantool \
    --rcfile="" \
    --logging=info \
    --interface=verilator \
    --verilator-bin=$BIN_DIR/hw/top_englishbreakfast/Vchip_englishbreakfast_verilator \
    --verilator-rom="$(find bazel-out/* -name 'test_rom_sim_verilator.32.vmem')" \
    --verilator-flash="$(find bazel-out/* -name 'aes_smoketest_prog_sim_verilator.64.scr.vmem')" \
    console \
    --exit-failure="(FAIL|FAULT).*\n" \
    --exit-success="PASS.*\n" \
    --timeout=3600s
