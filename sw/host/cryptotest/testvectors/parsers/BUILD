# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_binary", "py_library")
load("@ot_python_deps//:requirements.bzl", "requirement")

py_library(
    name = "cryptotest_util",
    srcs = ["cryptotest_util.py"],
)

py_binary(
    name = "nist_aes_parser",
    srcs = ["nist_aes_parser.py"],
    visibility = ["//visibility:public"],
    deps = [
        ":cryptotest_util",
        requirement("jsonschema"),
    ],
)
