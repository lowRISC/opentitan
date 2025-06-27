# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "freertos",
    srcs = ["@freertos//:srcs"],
    deps = [
        "//sw/device/lib/testing/test_framework:freertos_config",
        "@freertos//:hdrs",
    ],
)
