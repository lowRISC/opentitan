# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# List of self-checking test ROM images, which return PASS or FAIL after
# completion.
#
# Each list entry is a dict with the following keys:
#
# name:
#   Name of the test (required)
# verilator_extra_args:
#   A list of additional command-line arguments passed to the Verilator
#   simulation (optional).
# targets:
#   List of targets for which the test is executed. The test will be executed
#   on all targets if not given (optional).
TEST_ROMS_SELFCHECKING = [
    {
        "name": "mask_rom_epmp_test",
        "targets": ["sim_verilator"],
        "test_dir": "sw/device/silicon_creator/mask_rom",
    },
]
