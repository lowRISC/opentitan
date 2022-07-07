# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

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
