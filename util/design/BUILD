# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")
load("@rules_python//python:defs.bzl", "py_binary")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "prince",
    srcs = ["prince.py"],
)

py_library(
    name = "secded_gen",
    srcs = ["secded_gen.py"],
    data = ["//util/design/data:secded_cfg.hjson"],
    deps = [requirement("hjson")],
)

py_binary(
    name = "gen-flash-img",
    srcs = ["gen-flash-img.py"],
    deps = [
        ":secded_gen",
        "//util/design/lib:common",
        "//util/design/lib:otp_mem_map",
        "//util/design/lib:present",
        requirement("pyfinite"),
    ],
)

py_binary(
    name = "gen-lc-state-enc",
    srcs = ["gen-lc-state-enc.py"],
    data = ["//hw/ip/lc_ctrl/data:lc_ctrl_state.hjson"],
    imports = ["."],
    deps = [
        ":secded_gen",
        "//util/design/lib:common",
        "//util/design/lib:lc_st_enc",
        requirement("hjson"),
        requirement("mako"),
    ],
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

py_binary(
    name = "sparse-fsm-encode",
    srcs = ["sparse-fsm-encode.py"],
    imports = ["."],
    deps = ["//util/design/lib:common"],
)

py_test(
    name = "sparse-fsm-encode-test",
    srcs = ["sparse-fsm-encode-test.py"],
    deps = [":sparse-fsm-encode"],
)
