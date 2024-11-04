# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

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
    "cw310_params",
    "dv_params",
    "fpga_params",
    "opentitan_test",
    "verilator_params",
)

package(default_visibility = ["//visibility:public"])

rom_e2e_keymgr_init_configs = [
    {
        "name": "otp_meas",
        "value": CONST.HARDENED_TRUE,
    },
    {
        "name": "otp_no_meas",
        "value": CONST.HARDENED_FALSE,
    },
    {
        "name": "otp_invalid_meas",
        "value": 0,
    },
]

[
    otp_json(
        name = "otp_json_keymgr_{}".format(config["name"]),
        partitions = [
            otp_partition(
                name = "OWNER_SW_CFG",
                items = {
                    "OWNER_SW_CFG_ROM_KEYMGR_OTP_MEAS_EN": otp_hex(config["value"]),
                },
            ),
        ],
    )
    for config in rom_e2e_keymgr_init_configs
]

[
    otp_image(
        name = "otp_img_keymgr_{}".format(config["name"]),
        src = "//hw/ip/otp_ctrl/data:otp_json_rma",
        overlays = STD_OTP_OVERLAYS + [":otp_json_keymgr_{}".format(config["name"])],
        visibility = ["//visibility:private"],
    )
    for config in rom_e2e_keymgr_init_configs
]

[
    opentitan_test(
        name = "rom_e2e_keymgr_init_{}".format(config["name"]),
        srcs = [":rom_e2e_keymgr_init_test.c"],
        dv = dv_params(
            otp = ":otp_img_keymgr_{}".format(config["name"]),
            rom = "//sw/device/silicon_creator/rom:mask_rom",
        ),
        ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
            "//hw/top_earlgrey:sim_dv": None,
            "//hw/top_earlgrey:sim_verilator": None,
        },
        fpga = fpga_params(
            otp = ":otp_img_keymgr_{}".format(config["name"]),
        ),
        manifest = "//sw/device/silicon_creator/rom_ext:manifest",
        verilator = verilator_params(
            timeout = "eternal",
            otp = ":otp_img_keymgr_{}".format(config["name"]),
            rom = "//sw/device/silicon_creator/rom:mask_rom",
        ),
        deps = [
            "//sw/device/lib/dif:keymgr",
            "//sw/device/lib/testing:keymgr_testutils",
            "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:hmac",
            "//sw/device/silicon_creator/lib/drivers:otp",
        ],
    )
    for config in rom_e2e_keymgr_init_configs
]

test_suite(
    name = "keymgr_init",
    tags = ["manual"],
    tests = [
        "rom_e2e_keymgr_init_{}".format(config["name"])
        for config in rom_e2e_keymgr_init_configs
    ],
)
