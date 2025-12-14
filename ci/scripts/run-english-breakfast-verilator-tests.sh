#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Only a single test is supported on English Breakfast (EB).
# Currently, Bazel cannot build the EB Verilator model, so we only build the test with Bazel and then use opentitantool directly
# EB Verilator model is built in a previous CI step

set -e

# Increase the test_timeout due to slow performance on CI

./bazelisk.sh test \
    --build_tests_only=true \
    --test_timeout=2400,2400,3600,-1 \
    --local_test_jobs=8 \
    --local_resources=cpu=8 \
    --test_tag_filters=verilator,-broken \
    --test_output=errors \
    --//hw:verilator_options=--threads,1 \
    --//hw:make_options=-j,8 \
    --//hw/top=englishbreakfast \
    //sw/device/tests:aes_smoketest_sim_verilator \
    //sw/device/tests:uart_smoketest_sim_verilator \
    //sw/device/tests:crt_test_sim_verilator \
    //sw/device/tests:flash_ctrl_test_sim_verilator
