# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
    "opentitan_test",
)
load(
    "//sw/device/silicon_creator/rom_ext:defs.bzl",
    "ROM_EXT_VARIATIONS",
)

package(default_visibility = ["//visibility:public"])

[
    opentitan_test(
        name = "no_refresh_{}_test".format(variation),
        srcs = ["no_refresh_test.c"],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        },
        fpga = fpga_params(
            exit_failure = "Rebooting[\\s\\S]*CDI_1 certificate not valid[\\s\\S]*Rebooted",
            exit_success = "Rebooted\r\n",
            rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_{}_slot_a".format(variation),
        ),
        deps = [
            "//sw/device/lib/base:status",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:retention_sram",
            "//sw/device/silicon_creator/lib/drivers:rstmgr",
        ],
    )
    for variation in ROM_EXT_VARIATIONS.keys()
]
