# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "common",
    srcs = ["common.py"],
    imports = ["../../"],
    deps = [
        "//util/topgen",
    ],
)

py_library(
    name = "lc_st_enc",
    srcs = ["LcStEnc.py"],
    imports = ["../../"],
    deps = [
        ":common",
        "//util/topgen",
        requirement("pycryptodome"),
    ],
)

py_library(
    name = "otp_mem_map",
    srcs = ["OtpMemMap.py"],
    # Since this module is used by the `gen-otp-img.py` script, which is invoked
    # manually (by dvsim.py), and imported by the `gen-flash-img.py` script,
    # which is invoked automatically (via Bazel), we cannot use full package
    # includes within this module yet. Adding `util/design` to the imports path,
    # temporarily resovles this issue until the entire hw/ subtree can be
    # Bazelfied.
    imports = [
        "../",
        "../../",
    ],
    deps = [
        ":common",
        "//util/design/mubi:prim_mubi",
        "//util/topgen",
        requirement("tabulate"),
    ],
)

py_library(
    name = "otp_mem_img",
    srcs = ["OtpMemImg.py"],
    imports = ["../../"],
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
