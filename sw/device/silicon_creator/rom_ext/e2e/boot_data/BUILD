# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

opentitan_test(
    name = "redundancy_fix_test",
    srcs = ["redundancy_fix_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
    },
    fpga = fpga_params(
        # Clear the FPGA so the boot data is empty which needs redundancy fix.
        testopt_clear_before_test = "True",
    ),
    deps = [
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)
