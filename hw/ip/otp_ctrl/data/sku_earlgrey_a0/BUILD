# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otp.bzl", "otp_image_header", "otp_json")

package(default_visibility = ["//visibility:public"])

# Dummy partition used in `otp_image_header` targets.
otp_json(
    name = "otp_json_baseline",
    seed = "85452983286950371191603618368782861611109037138182535346147818831008789508651",
)

otp_image_header(
    name = "otp_img_sku_earlgrey_a0_stage_individualize",
    src = ":otp_json_baseline",
    overlays = [
        "//hw/ip/otp_ctrl/data:otp_json_creator_sw_cfg",
        "//hw/ip/otp_ctrl/data:otp_json_owner_sw_cfg",
        "//hw/ip/otp_ctrl/data:otp_json_alert_digest_cfg",
    ],
)
