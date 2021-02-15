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
        "name": "dif_otbn_smoketest_rtl",
        "binary_name": "dif_otbn_smoketest",
        "verilator_extra_args": ['+OTBN_USE_MODEL=0'],
    },
    {
        "name": "dif_otbn_smoketest_model",
        "binary_name": "dif_otbn_smoketest",
        "verilator_extra_args": ['+OTBN_USE_MODEL=1'],
        "targets": ["sim_verilator"],
    },
    # The OTBN end-to-end tests can be run in simulation, but take a long time
    # there. Run them on FPGAs only for faster test results.
    {
        "name": "otbn_rsa_test",
        "targets": ["fpga_nexysvideo"],
    },
    {
        "name": "otbn_ecdsa_p256_test",
        "targets": ["fpga_nexysvideo"],
    },
    {
        "name": "dif_aes_smoketest",
    },
    {
        "name": "dif_otp_ctrl_smoketest",
    },
    {
        "name": "dif_plic_smoketest",
    },
    {
        "name": "dif_rstmgr_smoketest",
    },
    {
        "name": "dif_rv_timer_smoketest",
    },
    {
        "name": "dif_uart_smoketest",
    },
    {
        "name": "dif_clkmgr_smoketest",
    },
    {
        "name": "flash_ctrl_test",
    },
    {
        "name": "pmp_smoketest_napot",
    },
    {
        "name": "pmp_smoketest_tor",
    },
    {
        "name": "sha256_test",
    },
    {
        "name": "usbdev_test",
        "targets": ["sim_verilator"],
    },
    # Cannot run on sim_verilator due to the differences in the top level.
    {
        "name": "dif_gpio_smoketest",
        "targets": ["fpga_nexysvideo"],
    },
]
