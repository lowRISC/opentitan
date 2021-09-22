# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

cc_library(
    name = "flash_ctrl",
    srcs = ["flash_ctrl.c"],
    hdrs = ["flash_ctrl.h"],
    deprecation = "Deprecated pre-DIF code. We prefer you use the DIFs.",
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
    ],
)

cc_library(
    name = "irq",
    srcs = [
        "handler.c",
        "irq.c",
    ],
    hdrs = [
        "handler.h",
        "irq.h",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
        "//sw/device/lib/runtime:log",
    ],
)

cc_library(
    name = "pinmux",
    srcs = ["pinmux.c"],
    hdrs = ["pinmux.h"],
    deprecation = "Deprecated pre-DIF code. We prefer you use the DIFs.",
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/ip/pinmux/data/autogen:pinmux_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base",
    ],
)
