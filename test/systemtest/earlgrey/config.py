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
        "name": "otbn_smoketest_rtl",
        "binary_name": "otbn_smoketest",
        "verilator_extra_args": ['+OTBN_USE_MODEL=0'],
        "targets": ["sim_verilator"],
    },
    {
        "name": "otbn_smoketest_model",
        "binary_name": "otbn_smoketest",
        "verilator_extra_args": ['+OTBN_USE_MODEL=1'],
        "targets": ["sim_verilator"],
    },
    {
        "name": "otbn_randomness_test",
        # TODO: Run this test also against the ISS once URND and RND are
        # implemented.
        "targets": ["sim_verilator", "fpga_cw310"],
    },
    {
        "name": "otbn_irq_test",
        "targets": ["sim_verilator", "fpga_cw310"],
    },
    # The OTBN end-to-end tests can be run in simulation, but take a long time
    # there. Run them on the CW310 FPGA board only for faster test results.
    {
        "name": "otbn_rsa_test",
        "targets": ["fpga_cw310"],
    },
    {
        "name": "otbn_ecdsa_op_irq_test",
        "targets": ["fpga_cw310"],
    },
    {
        "name": "aes_smoketest",
        "targets": ["sim_verilator", "fpga_cw310", "fpga_nexysvideo"],
    },
    {
        "name": "aon_timer_smoketest",
        "targets": ["sim_verilator", "fpga_cw310"],
    },
    {
        "name": "otp_ctrl_smoketest",
        "targets": ["sim_verilator", "fpga_cw310"],
    },
    {
        "name": "rv_plic_smoketest",
        "targets": ["sim_verilator", "fpga_cw310"],
    },
    {
        "name": "pwrmgr_smoketest",
        "targets": ["sim_verilator", "fpga_cw310"],
    },
    {
        "name": "rstmgr_smoketest",
        "targets": ["sim_verilator", "fpga_cw310", "fpga_nexysvideo"],
    },
    {
        "name": "rv_timer_smoketest",
        "targets": ["sim_verilator", "fpga_cw310"],
    },
    {
        "name": "uart_smoketest",
        "targets": ["sim_verilator", "fpga_cw310", "fpga_nexysvideo"],
    },
    {
        "name": "clkmgr_smoketest",
        "targets": ["sim_verilator", "fpga_cw310", "fpga_nexysvideo"],
    },
    {
        "name": "sram_ctrl_smoketest",
        "targets": ["sim_verilator", "fpga_cw310", "fpga_nexysvideo"],
    },
    # TODO(lowrisc/opentitan#7505): Debug CSRNG generate bits mismatch.
    # {
    #    "name": "csrng_smoketest",
    #   "targets": ["sim_verilator", "fpga_cw310"],
    # },
    # TODO(lowrisc/opentitan#10092): Remove dependency on uncontrolled
    # environment.
    # {
    #     "name": "entropy_src_smoketest",
    #     "targets": ["sim_verilator", "fpga_cw310"],
    # },
    {
        "name": "kmac_smoketest",
        "targets": ["sim_verilator", "fpga_cw310"],
    },
    {
        "name": "kmac_mode_cshake_test",
    },
    {
        "name": "kmac_mode_kmac_test",
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
        "name": "gpio_smoketest",
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
        "name": "sw_silicon_creator_lib_driver_retention_sram_functest",
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
    {
        "name": "sw_silicon_creator_lib_sigverify_functest",
        "test_dir": "sw/device/silicon_creator/testing",
        # Not running on sim_verilator because this test takes a long time to complete.
        "targets": ["fpga_cw310", "fpga_nexysvideo"],
    },
    {
        "name": "sw_silicon_creator_lib_driver_watchdog_functest",
        "test_dir": "sw/device/silicon_creator/testing",
        # TODO(lowRISC/opentitan#6965) This test resets the chip and appears to
        # cause a test failure on FPGA boards.  Restrict this test to
        # verilator for now.
        "targets": ["sim_verilator"],
    },
    {
        "name": "sw_silicon_creator_lib_irq_asm_functest",
        "test_dir": "sw/device/silicon_creator/testing",
        # TODO(lowRISC/opentitan#6965) This test resets the chip and appears to
        # cause a test failure on FPGA boards.  Restrict this test to
        # verilator for now.
        "targets": ["sim_verilator"],
    },
    {
        "name": "sw_silicon_creator_lib_boot_data_functest",
        "test_dir": "sw/device/silicon_creator/testing",
        # This test takes a long time to run in simulation.
        "targets": ["fpga_cw310"],
    },
]
