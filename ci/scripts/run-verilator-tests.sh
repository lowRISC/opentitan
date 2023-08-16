#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

#set -e

# Increase the test_timeout due to slow performance on CI

ci/bazelisk.sh build \
    --build_tests_only=true \
    --test_timeout=2400,2400,3600,-1 \
    --local_test_jobs=8 \
    --local_cpu_resources=8 \
    --test_tag_filters=verilator,-broken \
    --test_output=errors \
    --//hw:verilator_options=--threads,1 \
    --//hw:make_options=-j,8 \
    --execution_log_json_file=foo.json \
    //sw/device/silicon_creator/lib:irq_asm_functest_sim_verilator \
    -s --sandbox_debug --verbose_failures \
    --experimental_ui_max_stdouterr_bytes=4000000

    #//sw/device/tests:aes_smoketest_sim_verilator \
    #//sw/device/tests:uart_smoketest_sim_verilator \
    #//sw/device/tests:crt_test_sim_verilator \
    #//sw/device/tests:otbn_randomness_test_sim_verilator \
    #//sw/device/tests:otbn_irq_test_sim_verilator \
    #//sw/device/tests:kmac_mode_cshake_test_sim_verilator \
    #//sw/device/tests:kmac_mode_kmac_test_sim_verilator \
    #//sw/device/tests:flash_ctrl_test_sim_verilator \
    #//sw/device/tests:usbdev_test_sim_verilator \
    #//sw/device/silicon_creator/lib/drivers:hmac_functest_sim_verilator \
    #//sw/device/silicon_creator/lib/drivers:uart_functest_sim_verilator \
    #//sw/device/silicon_creator/lib/drivers:retention_sram_functest_sim_verilator \
    #//sw/device/silicon_creator/lib/drivers:alert_functest_sim_verilator \
    #//sw/device/silicon_creator/lib/drivers:watchdog_functest_sim_verilator \
    #//sw/device/silicon_creator/lib:irq_asm_functest_sim_verilator \
    #//sw/device/silicon_creator/rom:rom_epmp_test_sim_verilator

echo "######################################################################"
cd /root/.cache/bazel/_bazel_root/5e4f8c833cf3a422fdf6ca333dd151d7/execroot/lowrisc_opentitan || exit 1
find .
echo "######################################################################"
