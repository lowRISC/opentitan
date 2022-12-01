# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_binary")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "bitstream_bisect_support",
    deps = [
        "//rules/scripts:bitstreams_workspace",
        requirement("typer"),
        requirement("rich"),
    ],
)

py_binary(
    name = "bitstream_bisect",
    srcs = ["bitstream_bisect.py"],
    deps = [":bitstream_bisect_support"],
)

py_test(
    name = "bitstream_bisect_test",
    srcs = [
        "bitstream_bisect.py",
        "bitstream_bisect_test.py",
    ],
    deps = [":bitstream_bisect_support"],
)
