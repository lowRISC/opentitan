# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//third_party/zephyr:rules.bzl", "devicetree_library")

package(default_visibility = ["//visibility:public"])

devicetree_library(
    name = "cw310_devicetree",
    src = "earlgrey-cw310.dts",
    bindings = [
        "@zephyr//:dt_bindings",
        "//hw/dt_bindings",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen:earlgrey_devicetree",
    ],
)
