# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")
load("@rules_python//python:defs.bzl", "py_test")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "doc_files",
    srcs = glob(["**/*.md"]),
)

py_test(
    name = "parse_formal_report_test",
    size = "small",
    srcs = ["parse_formal_report_test.py"],
    data = ["//hw/formal/tools:report_parser_test_data"],
    deps = [requirement("hjson")],
)
