# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//hw/top:defs.bzl", "opentitan_select_top")

package(default_visibility = ["//visibility:public"])

# Setting for whether we are building "host" or "device" code.
constraint_setting(name = "target")

constraint_value(
    name = "host",
    constraint_setting = "target",
)

constraint_value(
    name = "device",
    constraint_setting = "target",
)

# Base OpenTitan platform for device code. Every platform should
# inherit from that. This is the default platform for tops if not
# overriden by the top.
platform(
    name = "opentitan_base_platform",
    constraint_values = [
        "@platforms//cpu:riscv32",
        "@platforms//os:none",
        ":device",
    ],
)
