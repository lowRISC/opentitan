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
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
    ],
)

cc_library(
    name = "ibex_peri",
    srcs = ["ibex_peri.c"],
    hdrs = ["ibex_peri.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
    ],
)

cc_library(
    name = "irq",
    srcs = ["irq.c"],
    hdrs = ["irq.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/base:csr",
    ],
)

cc_library(
    name = "usb",
    srcs = [
        "usb_controlep.c",
        "usbdev.c",
    ],
    hdrs = [
        "usb_consts.h",
        "usb_controlep.h",
        "usbdev.h",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/ip/usbdev/data:usbdev_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
    ],
)

cc_library(
    name = "usb_simpleserial",
    srcs = ["usb_simpleserial.c"],
    hdrs = ["usb_simpleserial.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [":usb"],
)
