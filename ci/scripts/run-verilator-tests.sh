#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

# Increase the test_timeout due to slow performance on CI

./bazelisk.sh query "filter('sim_verilator\_.*\_smoketest', tests(//sw/device/...))" | \
xargs ci/bazelisk.sh test \
    --build_tests_only=true \
    --test_timeout=2400,2400,3600,-1 \
    --local_test_jobs=4 \
    --local_cpu_resources=4 \
    --test_tag_filters=verilator,-failing_verilator,-broken \
    --test_output=errors \
    --//hw:verilator_options=--threads,1 \
    //sw/device/tests:sim_verilator_crt_test \
    //sw/device/tests:sim_verilator_otbn_randomness_test \
    //sw/device/tests:sim_verilator_otbn_irq_test \
    //sw/device/tests:sim_verilator_kmac_mode_cshake_test \
    //sw/device/tests:sim_verilator_kmac_mode_kmac_test \
    //sw/device/tests:sim_verilator_flash_ctrl_test \
    //sw/device/tests:sim_verilator_usbdev_test \
    //sw/device/silicon_creator/lib/drivers:sim_verilator_hmac_functest \
    //sw/device/silicon_creator/lib/drivers:sim_verilator_uart_functest \
    //sw/device/silicon_creator/lib/drivers:sim_verilator_retention_sram_functest \
    //sw/device/silicon_creator/lib/drivers:sim_verilator_alert_functest \
    //sw/device/silicon_creator/lib/drivers:sim_verilator_watchdog_functest \
    //sw/device/silicon_creator/lib:sim_verilator_irq_asm_functest
