# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_library")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "ip",
    srcs = ["ip.py"],
)

filegroup(
    name = "tpl_files",
    srcs = glob(["templates/*.tpl"]),
)
