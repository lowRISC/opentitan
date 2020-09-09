# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Self-checking test applications, which return PASS or FAIL after completion,
# usable on all targets.
TEST_APPS_SELFCHECKING = [
    "aes_test",
    "crt_test",
    "dif_plic_sanitytest",
    "dif_rv_timer_sanitytest",
    "dif_uart_sanitytest",
    "flash_ctrl_test",
    "pmp_sanitytest_napot",
    "pmp_sanitytest_tor",
    "sha256_test",
]

# Self-checking applications running on the Verilator simulation
TEST_APPS_SELFCHECKING_SIM_VERILATOR = TEST_APPS_SELFCHECKING + [
    "usbdev_test",
]
