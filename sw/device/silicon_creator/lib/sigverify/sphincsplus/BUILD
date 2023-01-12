# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "address",
    srcs = ["address.c"],
    hdrs = ["address.h"],
    deps = [
        ":params",
        "//sw/device/lib/base:memory",
    ],
)

cc_library(
    name = "params",
    hdrs = ["params.h"],
)
