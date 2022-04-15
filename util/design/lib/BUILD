# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "common",
    srcs = ["common.py"],
)

py_library(
    name = "lc_st_enc",
    srcs = ["LcStEnc.py"],
    deps = [
        ":common",
        requirement("pycryptodome"),
    ],
)

py_library(
    name = "otp_mem_map",
    srcs = ["OtpMemMap.py"],
    deps = [
        ":common",
        "//util/design/mubi:prim_mubi",
        requirement("tabulate"),
    ],
)

py_library(
    name = "otp_mem_img",
    srcs = ["OtpMemImg.py"],
    deps = [
        ":common",
        ":lc_st_enc",
        ":otp_mem_map",
        ":present",
        "//util/design/mubi:prim_mubi",
        requirement("pycryptodome"),
    ],
)

py_library(
    name = "present",
    srcs = ["Present.py"],
)
