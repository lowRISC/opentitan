# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otp.bzl", "otp_image_consts", "otp_json")

package(default_visibility = ["//visibility:public"])

# Dummy partition used in `otp_image_header` targets.
otp_json(
    name = "otp_json_baseline",
    seed = "94259314771464387",
)

otp_image_consts(
    name = "otp_img_consts_c_file",
    src = ":otp_json_baseline",
    overlays = [
        "//hw/ip/otp_ctrl/data:otp_json_creator_sw_cfg",
        "//hw/ip/otp_ctrl/data:otp_json_owner_sw_cfg",
        "//hw/ip/otp_ctrl/data:otp_json_alert_digest_cfg",
    ],
)

cc_library(
    name = "otp_img_consts",
    srcs = [":otp_img_consts_c_file"],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/silicon_creator/manuf/lib:otp_img_types",
    ],
)
