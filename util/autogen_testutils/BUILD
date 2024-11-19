# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_library")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "tpl_files",
    srcs = glob(["templates/*.tpl"]),
)

py_library(
    name = "autogen_testutils",
    srcs = ["gen.py"],
    data = [":tpl_files"],
    deps = ["//util/topgen:lib"],
)
