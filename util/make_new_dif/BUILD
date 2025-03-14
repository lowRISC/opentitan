# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")
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

py_library(
    name = "make_new_dif",
    srcs = ["ip.py"],
    data = [":tpl_files"],
    # This makes `make_new_dif` importable as a python package.
    imports = [".."],
    deps = [
        ":ip",
        requirement("hjson"),
    ],
)
