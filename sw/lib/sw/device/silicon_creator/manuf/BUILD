# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan.bzl",
    "OPENTITAN_CPU",
)

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "sram_start_headers",
    hdrs = ["sram_start.h"],
)

cc_library(
    name = "sram_start",
    srcs = ["sram_start.S"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":sram_start_headers",
        "//sw/lib/sw/device/crt",
    ],
)

cc_library(
    name = "otp_img_types",
    hdrs = ["otp_img_types.h"],
)

exports_files(glob(["*.c", "*.h"]))
