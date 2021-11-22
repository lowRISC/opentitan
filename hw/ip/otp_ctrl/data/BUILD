# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:autogen.bzl", "autogen_hjson_header", "otp_image")

autogen_hjson_header(
    name = "otp_ctrl_regs",
    srcs = [
        "otp_ctrl.hjson",
    ],
)

otp_image(
    name = "rma_image_verilator",
    src = "otp_ctrl_img_rma.hjson",
    deps = [
        "otp_ctrl_mmap.hjson",
        "//hw/ip/lc_ctrl/data:lc_ctrl_state.hjson",
    ],
)

filegroup(
    name = "all_files",
    srcs = glob(["**"]),
)
