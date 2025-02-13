# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU", "opentitan_binary")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "rescue",
    srcs = ["rescue.c"],
    hdrs = ["rescue.h"],
    deps = [
        ":xmodem",
        "//hw/top:flash_ctrl_c_regs",
        "//sw/device/lib/base:memory",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib:dbg_print",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
        "//sw/device/silicon_creator/lib/ownership:owner_block",
    ],
)

cc_library(
    name = "xmodem",
    srcs = ["xmodem.c"],
    hdrs = ["xmodem.h"],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/drivers:uart",
    ],
)

cc_library(
    name = "xmodem_testlib",
    srcs = [
        "xmodem.c",
        "xmodem.h",
    ],
    hdrs = ["xmodem_testlib.h"],
    defines = ["XMODEM_TESTLIB=1"],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib:error",
    ],
)
