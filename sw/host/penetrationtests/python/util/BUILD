# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")
load("@rules_python//python:defs.bzl", "py_library")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "utils",
    srcs = ["utils.py"],
)

py_library(
    name = "targets",
    srcs = ["targets.py"],
    deps = [
        requirement("pyserial"),
        ":hyperdebug",
    ],
)

py_library(
    name = "common_library",
    srcs = ["common_library.py"],
)

py_library(
    name = "hyperdebug",
    srcs = ["hyperdebug.py"],
)

py_library(
    name = "gdb_controller",
    srcs = ["gdb_controller.py"],
)

py_library(
    name = "dis_parser",
    srcs = ["dis_parser.py"],
)
