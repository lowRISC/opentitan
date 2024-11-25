# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:hw.bzl", "opentitan_ip")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "all_files",
    srcs = glob(["**"]) + [
        "//hw/ip/aes/data:all_files",
    ],
)

cc_library(
    name = "model",
    hdrs = [
        "model/aes.h",
        "model/aes_modes.h",
    ],
)

opentitan_ip(
    name = "aes",
    hjson = "//hw/ip/aes/data:hjson",
)
