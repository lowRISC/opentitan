#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

# Increase the test_timeout due to slow performance on CI

ci/bazelisk.sh test \
    --build_tests_only=true \
    --test_timeout=2400,2400,3600,-1 \
    --local_test_jobs=4 \
    --local_cpu_resources=4 \
    --test_tag_filters=verilator,-broken \
    --test_output=errors \
    --//hw:verilator_options=--threads,1 \
    --//hw:make_options=-j,4 \
    //sw/device/tests:aes_smoketest_sim_verilator \
    //sw/device/tests:uart_smoketest_sim_verilator \
    //sw/device/tests:crt_test_sim_verilator \
    //sw/device/tests:otbn_randomness_test_sim_verilator \
    //sw/device/tests:otbn_irq_test_sim_verilator \
    //sw/device/tests:kmac_mode_cshake_test_sim_verilator \
    //sw/device/tests:kmac_mode_kmac_test_sim_verilator \
    //sw/device/tests:flash_ctrl_test_sim_verilator \
    //sw/device/tests:usbdev_test_sim_verilator \
    //sw/device/silicon_creator/lib/drivers:hmac_functest_sim_verilator \
    //sw/device/silicon_creator/lib/drivers:uart_functest_sim_verilator \
    //sw/device/silicon_creator/lib/drivers:retention_sram_functest_sim_verilator \
    //sw/device/silicon_creator/lib/drivers:alert_functest_sim_verilator \
    //sw/device/silicon_creator/lib/drivers:watchdog_functest_sim_verilator \
    //sw/device/silicon_creator/lib:irq_asm_functest_sim_verilator \
    //sw/device/silicon_creator/rom:rom_epmp_test_sim_verilator
