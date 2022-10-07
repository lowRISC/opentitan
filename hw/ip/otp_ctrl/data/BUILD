# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:autogen.bzl", "autogen_hjson_header")
load("//rules:otp.bzl", "otp_image", "otp_json")
load("@rules_pkg//pkg:mappings.bzl", "pkg_files")

package(default_visibility = ["//visibility:public"])

autogen_hjson_header(
    name = "otp_ctrl_regs",
    srcs = [
        "otp_ctrl.hjson",
    ],
)

otp_json(
    name = "otp_ctrl_rma_json",
    lc_count = 8,
    lc_state = "RMA",
)

otp_image(
    name = "img_rma",
    src = ":otp_ctrl_rma_json",
)

otp_json(
    name = "otp_ctrl_dev_json",
    lc_count = 5,
    lc_state = "DEV",
)

otp_image(
    name = "img_dev",
    src = ":otp_ctrl_dev_json",
)

otp_json(
    name = "otp_ctrl_prod_json",
    lc_count = 5,
    lc_state = "PROD",
)

otp_image(
    name = "img_prod",
    src = ":otp_ctrl_prod_json",
)

filegroup(
    name = "all_files",
    srcs = glob(["**"]),
)

pkg_files(
    name = "package",
    srcs = [
        ":img_dev",
        ":img_prod",
        ":img_rma",
    ],
    prefix = "earlgrey/otp",
)
