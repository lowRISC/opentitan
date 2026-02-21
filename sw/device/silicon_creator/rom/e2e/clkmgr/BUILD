# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "opentitan_test",
)
load(
    "//rules:const.bzl",
    "CONST",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_hex",
    "otp_image",
    "otp_json",
    "otp_partition",
)
load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
    "opentitan_test",
)

otp_json(
    name = "otp_json_jitter_enabled",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                "CREATOR_SW_CFG_JITTER_EN": otp_hex(CONST.MUBI4_TRUE),
            },
        ),
    ],
)

otp_image(
    name = "otp_img_jitter_enabled",
    src = "//hw/ip/otp_ctrl/data:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [":otp_json_jitter_enabled"],
)

JITTER_TESTCASES = [
    {
        "name": "disabled",
        "fpga": fpga_params(),
        "defines": ["TEST_JITTER_DISABLED"],
    },
    {
        "name": "enabled",
        "fpga": fpga_params(
            otp = ":otp_img_jitter_enabled",
            tags = ["coverage"],
        ),
        "defines": ["TEST_JITTER_ENABLED"],
    },
]

[
    opentitan_test(
        name = "jitter_{}_test".format(testcase["name"]),
        srcs = ["jitter_test.c"],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        },
        fpga = testcase["fpga"],
        local_defines = testcase["defines"],
        deps = [
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/dif:base",
            "//sw/device/lib/dif:clkmgr",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for testcase in JITTER_TESTCASES
]
