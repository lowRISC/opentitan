# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_library")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "raclgen",
    srcs = [
        "__init__.py",
        "lib.py",
    ],
    deps = [
        "//util/reggen:ip_block",
        "//util/reggen:md_helpers",
        "//util/reggen:multi_register",
        "//util/reggen:register",
        "//util/reggen:validate",
        "//util/reggen:window",
        requirement("hjson"),
    ],
)
