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
        "tagets": ["sim_verilator"],
    },
    {
        "name": "otbn_smoketest_rtl",
        "binary_name": "otbn_smoketest",
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
        "targets": ["sim_verilator"],
    },
    {
        "name": "aes_smoketest",
        "targets": ["sim_verilator"],
    },
    {
        "name": "aon_timer_smoketest",
        "targets": ["sim_verilator"],
    },
    {
        "name": "otp_ctrl_smoketest",
        "targets": ["sim_verilator"],
    },
    {
        "name": "rv_plic_smoketest",
        "targets": ["sim_verilator"],
    },
    {
        "name": "pwrmgr_smoketest",
        "targets": ["sim_verilator"],
    },
    {
        "name": "rstmgr_smoketest",
        "targets": ["sim_verilator"],
    },
    {
        "name": "rv_timer_smoketest",
        "targets": ["sim_verilator"],
    },
    {
        "name": "uart_smoketest",
        "targets": ["sim_verilator"],
    },
    {
        "name": "clkmgr_smoketest",
        "targets": ["sim_verilator"],
    },
    {
        "name": "sram_ctrl_smoketest",
        "targets": ["sim_verilator"],
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
        "targets": ["sim_verilator"],
    },
    {
        "name": "kmac_mode_cshake_test", # Passing on cw310 when coordinated by bazel
    },
    {
        "name": "kmac_mode_kmac_test", # Passing on cw310 when coordinated by bazel
    },
    {
        "name": "flash_ctrl_test",
        "targets": ["sim_verilator"],
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
    {
        "name": "sw_silicon_creator_lib_driver_hmac_functest", # Passing on cw310 when coordinated by bazel
        "test_dir": "sw/device/silicon_creator/testing",
    },
    {
        "name": "sw_silicon_creator_lib_driver_uart_functest", # Passing on cw310 when coordinated by bazel
        "test_dir": "sw/device/silicon_creator/testing",
    },
    {
        "name": "sw_silicon_creator_lib_driver_retention_sram_functest", # Passing on cw310 when coordinated by bazel
        "test_dir": "sw/device/silicon_creator/testing",
    },
    {
        "name": "sw_silicon_creator_lib_driver_alert_functest", # Passing on cw310 when coordinated by bazel
        "test_dir": "sw/device/silicon_creator/testing",
        "targets": ["sim_verilator"],
    },
    {
        "name": "sw_silicon_creator_lib_driver_watchdog_functest",
        "test_dir": "sw/device/silicon_creator/testing",
        "targets": ["sim_verilator"],
    },
    {
        "name": "sw_silicon_creator_lib_irq_asm_functest",
        "test_dir": "sw/device/silicon_creator/testing",
        "targets": ["sim_verilator"],
    },
]
