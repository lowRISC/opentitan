# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_library")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "ipgen",
    srcs = [
        "__init__.py",
        "lib.py",
        "renderer.py",
    ],
    deps = [
        "//util/reggen:gen_rtl",
        "//util/reggen:lib",
        "//util/reggen:params",
        requirement("hjson"),
        requirement("mako"),
    ],
)

py_test(
    name = "test_render",
    srcs = ["tests/test_render.py"],
    deps = [
        ":ipgen",
        requirement("pytest"),
    ],
)
