# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# List of self-checking test applications, which return PASS or FAIL after
# completion.
#
# Each list entry is a dict with the following keys:
#
# name:
#   Name of the test (required)
# binary_name:
#   Basename of the test binary. Default: name (optional)
# verilator_extra_args:
#   A list of additional command-line arguments passed to the Verilator
#   simulation (optional).
# targets:
#   List of targets for which the test is executed. The test will be executed
#   on all targets if not given (optional).
TEST_APPS_SELFCHECKING = [
    {
        "name": "aes_test",
    },
    {
        "name": "crt_test",
    },
    {
        "name": "dif_otbn_sanitytest_rtl",
        "binary_name": "dif_otbn_sanitytest",
        "verilator_extra_args": ['+OTBN_USE_MODEL=0'],
    },
# Using the model in CI isn't possible until #4097 is resolved.
#    {
#        "name": "dif_otbn_sanitytest_model",
#        "binary_name": "dif_otbn_sanitytest",
#        "verilator_extra_args": ['+OTBN_USE_MODEL=1'],
#        "targets": ["sim_verilator"],
#    },
    {
        "name": "dif_plic_sanitytest",
    },
    {
        "name": "dif_rstmgr_sanitytest",
    },
    {
        "name": "dif_rv_timer_sanitytest",
    },
    {
        "name": "dif_uart_sanitytest",
    },
    {
        "name": "flash_ctrl_test",
    },
    {
        "name": "pmp_sanitytest_napot",
    },
    {
        "name": "pmp_sanitytest_tor",
    },
    {
        "name": "sha256_test",
    },
    {
        "name": "usbdev_test",
        "targets": ["sim_verilator"],
    },
]
