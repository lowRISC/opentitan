# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@bazel_skylib//lib:dicts.bzl",
    "dicts",
)
load(
    "//rules/opentitan:defs.bzl",
    "EARLGREY_SILICON_OWNER_ROM_EXT_ENVS",
    "EARLGREY_TEST_ENVS",
    "fpga_params",
    "opentitan_test",
    "silicon_params",
    "verilator_params",
)

package(default_visibility = ["//visibility:public"])

RESCUE_DEPS = [
    "//hw/top:flash_ctrl_c_regs",
    "//sw/device/lib/base:macros",
    "//sw/device/lib/base:memory",
    "//sw/device/silicon_creator/lib:manifest",
    "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
    "//sw/device/silicon_creator/lib/drivers:lifecycle",
    "//sw/device/silicon_creator/lib/drivers:pinmux",
    "//sw/device/silicon_creator/lib/drivers:retention_sram",
    "//sw/device/silicon_creator/lib/drivers:rstmgr",
    "//sw/device/silicon_creator/lib/ownership:owner_block",
]

cc_library(
    name = "rescue",
    hdrs = ["rescue.h"],
    deps = [
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib:dbg_print",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
        "//sw/device/silicon_creator/lib/ownership:datatypes",
    ],
)

cc_library(
    name = "rescue_xmodem",
    srcs = [
        "rescue.c",
        "rescue_xmodem.c",
    ],
    local_defines = ["RESCUE_USES_UART=1"],
    deps = [
        ":rescue",
        ":xmodem",
        "//sw/device/silicon_creator/lib/drivers:ibex",
    ] + RESCUE_DEPS,
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

cc_library(
    name = "dfu",
    srcs = [
        "dfu.c",
        "dfu_state_table.c",
    ],
    hdrs = [
        "dfu.h",
    ],
    deps = [
        ":rescue",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
        "//sw/device/silicon_creator/lib/drivers:usb",
    ],
)

cc_library(
    name = "rescue_usbdfu",
    srcs = [
        "rescue.c",
        "rescue_usb.c",
    ],
    local_defines = ["RESCUE_USES_UART=0"],
    deps = [
        ":dfu",
        ":rescue",
        "//sw/device/silicon_creator/lib/drivers:usb",
    ] + RESCUE_DEPS,
)

cc_library(
    name = "rescue_spidfu",
    srcs = [
        "rescue.c",
        "rescue_spi.c",
        "sfdp.c",
        "sfdp.h",
    ],
    local_defines = ["RESCUE_USES_UART=0"],
    deps = [
        ":dfu",
        ":rescue",
        "//sw/device/silicon_creator/lib/drivers:spi_device",
        "//sw/device/silicon_creator/lib/drivers:usb",
    ] + RESCUE_DEPS,
)

cc_library(
    name = "rescue_null",
    srcs = [
        "rescue.c",
        "rescue_null.c",
    ],
    local_defines = ["RESCUE_USES_UART=0"],
    deps = [
        ":rescue",
    ] + RESCUE_DEPS,
)
