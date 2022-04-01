# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])
load("@lowrisc_misc_linters_pip//:requirements.bzl", "requirement")

py_binary(
    name = "licence-checker",
    srcs = ["licence-checker.py"],
    deps = [
        requirement('hjson'),
        requirement('tabulate'),
    ],
)
