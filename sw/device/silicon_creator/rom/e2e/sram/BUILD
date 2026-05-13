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
                # Turn readback on for both retram and sram.
                "OWNER_SW_CFG_ROM_SRAM_READBACK_EN": otp_hex(CONST.MUBI4_TRUE << 4 | CONST.MUBI4_TRUE),
            },
        ),
    ],
)

# OTP images that enable the watchdog.
otp_image(
    name = "otp_img_readback_enable",
    src = "//hw/top_earlgrey/data/otp:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [":otp_json_readback_enable"],
)

_READBACK_TESTS = {
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
            "//hw/top:otp_ctrl_c_regs",
            "//hw/top:sram_ctrl_c_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:otp",
        ],
    )
    for name, param in _READBACK_TESTS.items()
]

test_suite(
    name = "sram_readback_test",
    tags = ["manual"],
    tests = [
        "sram_readback_{}_test".format(name)
        for name in _READBACK_TESTS.keys()
    ],
)

otp_json(
    name = "otp_json_renew_disabled",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                "CREATOR_SW_CFG_SRAM_KEY_RENEW_AND_INIT_EN": otp_hex(CONST.HARDENED_FALSE),
            },
        ),
    ],
)

otp_image(
    name = "otp_img_renew_disabled",
    src = "//hw/top_earlgrey/data/otp:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [":otp_json_renew_disabled"],
)

_RENEW_TESTS = {
    "default": {
        "otp": None,
    },
    "disabled": {
        "otp": ":otp_img_renew_disabled",
    },
}

[
    opentitan_test(
        name = "sram_key_renew_{}_test".format(name),
        srcs = ["sram_renew_test.c"],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        },
        fpga = fpga_params(
            otp = param["otp"],
        ),
        deps = [
            "//hw/top:otp_ctrl_c_regs",
            "//hw/top:sram_ctrl_c_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:otp",
        ],
    )
    for name, param in _RENEW_TESTS.items()
]

test_suite(
    name = "sram_key_renew_test",
    tags = ["manual"],
    tests = [
        "sram_key_renew_{}_test".format(name)
        for name in _RENEW_TESTS.keys()
    ],
)
