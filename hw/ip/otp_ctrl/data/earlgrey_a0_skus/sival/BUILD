# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:otp.bzl",
    "otp_image",
    "otp_image_consts",
    "otp_json",
)

package(default_visibility = ["//visibility:public"])

# Dummy partition used in `otp_image_consts` targets.
otp_json(
    name = "otp_json_baseline",
    seed = "85452983286950371191603618368782861611109037138182535346147818831008789508651",
)

# OTP SW Configuration for Test SKU.
otp_image_consts(
    name = "otp_sw_cfg_c_file",
    src = ":otp_json_baseline",
    overlays = [
        "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/generic:alert_digest_cfg",
        "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/generic:otp_json_creator_sw_cfg",
        "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/generic:otp_json_owner_sw_cfg",
    ],
)

cc_library(
    name = "otp_sw_cfg",
    srcs = [":otp_sw_cfg_c_file"],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/silicon_creator/manuf/lib:otp_img_types",
    ],
)

MISSION_MODE_OVERLAYS = [
    "//hw/ip/otp_ctrl/data:otp_json_hw_cfg",
    "//hw/ip/otp_ctrl/data:otp_json_fixed_secret0",
    "//hw/ip/otp_ctrl/data:otp_json_secret1",
    "//hw/ip/otp_ctrl/data:otp_json_fixed_secret2",
    "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/generic:alert_digest_cfg",
    "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/generic:otp_json_creator_sw_cfg",
    "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/generic:otp_json_owner_sw_cfg",
]

otp_image(
    name = "otp_img_prod_personalized",
    src = "//hw/ip/otp_ctrl/data:otp_json_prod",
    overlays = MISSION_MODE_OVERLAYS,
)

otp_image(
    name = "otp_img_prod_end_personalized",
    src = "//hw/ip/otp_ctrl/data:otp_json_prod_end",
    overlays = MISSION_MODE_OVERLAYS,
)

otp_image(
    name = "otp_img_dev_personalized",
    src = "//hw/ip/otp_ctrl/data:otp_json_dev",
    overlays = MISSION_MODE_OVERLAYS,
)
