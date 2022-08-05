# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "absl_status",
    hdrs = ["absl_status.h"],
)

cc_library(
    name = "status",
    hdrs = ["status.h"],
    deps = [
        ":absl_status",
        "//sw/device/lib/base:bitfield",
    ],
)
