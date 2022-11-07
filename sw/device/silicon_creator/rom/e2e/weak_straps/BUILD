# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load(":gpio.bzl", "strap_combinations_test")

strap_combinations_test(
    name = "e2e_weak_straps",
    rom = "//sw/device/silicon_creator/rom",
    tags = [
        "verilator",
    ],
)

strap_combinations_test(
    name = "sw_strap_value",
    rom = "//sw/device/lib/testing/test_rom",
    # The test_rom does not support checking the strength of
    # the GPIO input.  The following values are all equivalent
    # to 63 when read out of the GPIO peripheral without
    # performing the strength check by manipulating the pinmux.
    skip_value = [
        42,
        43,
        46,
        47,
        58,
        59,
        62,
    ],
    tags = [
        "verilator",
    ],
)
