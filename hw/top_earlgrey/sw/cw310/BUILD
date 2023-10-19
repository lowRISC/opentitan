# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "devicetables",
    srcs = [
        "dt_clock.c",
        "dt_pinctrl.c",
    ],
    copts = ["-flto=full"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/devicetables",
        "//sw/device/lib/devicetables:dt_api",
    ],
)
