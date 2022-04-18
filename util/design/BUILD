# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")
load("@rules_python//python:defs.bzl", "py_binary")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "secded_gen",
    srcs = ["secded_gen.py"],
    deps = [requirement("hjson")],
)

py_binary(
    name = "gen-flash-img",
    srcs = ["gen-flash-img.py"],
    deps = [":secded_gen"],
)

py_binary(
    name = "gen-otp-img",
    srcs = ["gen-otp-img.py"],
    imports = ["."],
    deps = [
        "//util/design/lib:common",
        "//util/design/lib:otp_mem_img",
        requirement("hjson"),
    ],
)
