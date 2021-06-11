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
        "name": "crt_test",
    },
    {
        "name": "dif_otbn_smoketest_rtl",
        "binary_name": "dif_otbn_smoketest",
        "verilator_extra_args": ['+OTBN_USE_MODEL=0'],
        "targets": ["sim_verilator"],
    },
    {
        "name": "dif_otbn_smoketest_model",
        "binary_name": "dif_otbn_smoketest",
        "verilator_extra_args": ['+OTBN_USE_MODEL=1'],
        "targets": ["sim_verilator"],
    },
    # The OTBN end-to-end tests can be run in simulation, but take a long time
    # there. Run them on the CW310 FPGA board only for faster test results.
    {
        "name": "otbn_rsa_test",
        "targets": ["fpga_cw310"],
    },
    {
        "name": "otbn_ecdsa_p256_test",
        "targets": ["fpga_cw310"],
    },
    {
        "name": "dif_aes_smoketest",
        "targets": ["sim_verilator", "fpga_cw310", "fpga_nexysvideo"],
    },
    {
        "name": "dif_aon_timer_smoketest",
        "targets": ["sim_verilator", "fpga_cw310"],
    },
    {
        "name": "dif_otp_ctrl_smoketest",
        "targets": ["sim_verilator", "fpga_cw310"],
    },
    {
        "name": "dif_plic_smoketest",
        "targets": ["sim_verilator", "fpga_cw310"],
    },
    # TODO(#6656): AST is not instantiated in chip_earlgrey_verilator.
    # {
    #     "name": "dif_pwrmgr_smoketest",
    # },
    {
        "name": "dif_rstmgr_smoketest",
        "targets": ["sim_verilator", "fpga_cw310", "fpga_nexysvideo"],
    },
    {
        "name": "dif_rv_timer_smoketest",
        "targets": ["sim_verilator", "fpga_cw310"],
    },
    {
        "name": "dif_uart_smoketest",
        "targets": ["sim_verilator", "fpga_cw310", "fpga_nexysvideo"],
    },
    {
        "name": "dif_clkmgr_smoketest",
        "targets": ["sim_verilator", "fpga_cw310", "fpga_nexysvideo"],
    },
    {
        "name": "dif_csrng_smoketest",
        "targets": ["sim_verilator", "fpga_cw310"],
    },
    {
        "name": "dif_entropy_smoketest",
        "targets": ["sim_verilator", "fpga_cw310"],
    },
    {
        "name": "dif_kmac_smoketest",
        "targets": ["sim_verilator", "fpga_cw310"],
    },
    {
        "name": "dif_kmac_cshake_smoketest",
    },
    {
        "name": "dif_kmac_kmac_smoketest",
    },
    {
        "name": "flash_ctrl_test",
        "targets": ["sim_verilator", "fpga_cw310", "fpga_nexysvideo"],
    },
    {
        "name": "pmp_smoketest_napot",
        "targets": ["sim_verilator", "fpga_cw310"],
    },
    {
        "name": "pmp_smoketest_tor",
        "targets": ["sim_verilator", "fpga_cw310"],
    },
    {
        "name": "usbdev_test",
        "targets": ["sim_verilator"],
    },
    # Cannot run on sim_verilator due to the differences in the top level.
    {
        "name": "dif_gpio_smoketest",
        "targets": ["fpga_cw310", "fpga_nexysvideo"],
    },
    {
        "name": "sw_silicon_creator_lib_driver_hmac_functest",
        "test_dir": "sw/device/silicon_creator/testing",
    },
    {
        "name": "sw_silicon_creator_lib_driver_uart_functest",
        "test_dir": "sw/device/silicon_creator/testing",
    },
    {
        "name": "sw_silicon_creator_lib_driver_alert_functest",
        "test_dir": "sw/device/silicon_creator/testing",
        # TODO(lowRISC/opentitan#6965) This test resets the chip and appears to
        # cause a test failure on FPGA boards.  Restrict this test to
        # verilator for now.
        "targets": ["sim_verilator"],
    },
]
