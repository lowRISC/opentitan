# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "command",
    srcs = ["command.c"],
    hdrs = ["command.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "chip_specific_startup",
    srcs = ["chip_specific_startup.c"],
    hdrs = ["chip_specific_startup.h"],
    deps = ["//sw/device/lib/ujson"],
)
