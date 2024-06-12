# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
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

package(default_visibility = ["//visibility:public"])

otp_json(
    name = "otp_json_readback_enable",
    partitions = [
        otp_partition(
            name = "OWNER_SW_CFG",
            items = {
                "OWNER_SW_CFG_ROM_SRAM_READBACK_EN": otp_hex(CONST.MUBI4_TRUE),
            },
        ),
    ],
)

# OTP images that enable the watchdog.
otp_image(
    name = "otp_img_readback_enable",
    src = "//hw/ip/otp_ctrl/data:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [":otp_json_readback_enable"],
)

_TESTS = {
    "default": {
        "otp": None,
    },
    "enabled": {
        "otp": ":otp_img_readback_enable",
    },
}

[
    opentitan_test(
        name = "sram_readback_{}_test".format(name),
        srcs = ["sram_readback_test.c"],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        },
        fpga = fpga_params(
            otp = param["otp"],
        ),
        deps = [
            "//hw/ip/otp_ctrl/data:otp_ctrl_c_regs",
            "//hw/ip/sram_ctrl/data:sram_ctrl_c_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:otp",
        ],
    )
    for name, param in _TESTS.items()
]

test_suite(
    name = "sram_readback_test",
    tags = ["manual"],
    tests = [
        "sram_readback_{}_test".format(name)
        for name in _TESTS.keys()
    ],
)
