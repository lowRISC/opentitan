# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_library")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "helper",
    srcs = ["helper.py"],
    deps = ["//util/topgen:lib"],
)

py_library(
    name = "ipgen_ext",
    srcs = ["ipgen_ext.py"],
    deps = [
        "//util/topgen:lib",
        requirement("jsonschema"),
    ],
)

filegroup(
    name = "tpl_files",
    srcs = glob(["**/*.tpl"]),
)

filegroup(
    name = "doc_files",
    srcs = [":README.md"],
)
