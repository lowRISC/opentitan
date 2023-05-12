# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "OPENTITAN_CPU")
load("//rules:opentitan_test.bzl", "opentitan_functest", "verilator_params")

# Export all headers.
exports_files(glob(["*.h"]))

cc_library(
    name = "datatypes",
    hdrs = ["datatypes.h"],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:status",
    ],
)
