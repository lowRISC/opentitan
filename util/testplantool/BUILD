# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_binary")
load("@ot_python_deps//:requirements.bzl", "all_requirements", "requirement")

package(default_visibility = ["//visibility:public"])

exports_files(glob(["**"]))

filegroup(
    name = "doc_files",
    srcs = glob(["**/*.md"]),
)

py_library(
    name = "testplanlib",
    srcs = ["testplanlib/lib.py"],
    deps = [
        requirement("hjson"),
        requirement("mako"),
    ],
)

py_binary(
    name = "testplantool",
    srcs = [
        "cli.py",
        "testplantool.py",
    ],
    deps = [
        ":testplanlib",
        requirement("click"),
    ],
)
