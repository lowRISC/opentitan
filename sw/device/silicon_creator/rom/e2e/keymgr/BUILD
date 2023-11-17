# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "dv_params",
    "hyper310_params",
    "opentitan_binary",
    "opentitan_test",
    "verilator_params",
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

opentitan_binary(
    name = "rom_e2e_keymgr_init_test",
    testonly = True,
    srcs = [":rom_e2e_keymgr_init_test.c"],
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys",
        "//hw/top_earlgrey:sim_dv",
        "//hw/top_earlgrey:sim_verilator",
    ],
    deps = [
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:otp",
    ],
)

rom_e2e_keymgr_init_configs = [
    {
        "name": "rom_ext_meas",
        "value": CONST.HARDENED_TRUE,
    },
    {
        "name": "rom_ext_no_meas",
        "value": CONST.HARDENED_FALSE,
    },
    {
        "name": "rom_ext_invalid_meas",
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
                    "OWNER_SW_CFG_ROM_KEYMGR_ROM_EXT_MEAS_EN": otp_hex(config["value"]),
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
        cw310 = cw310_params(
            binaries = {":rom_e2e_keymgr_init_test": "firmware"},
            otp = ":otp_img_keymgr_{}".format(config["name"]),
        ),
        dv = dv_params(
            binaries = {":rom_e2e_keymgr_init_test": "firmware"},
            otp = ":otp_img_keymgr_{}".format(config["name"]),
            rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:sim_dv": None,
            "//hw/top_earlgrey:sim_verilator": None,
        },
        hyper310 = hyper310_params(
            binaries = {":rom_e2e_keymgr_init_test": "firmware"},
            otp = ":otp_img_keymgr_{}".format(config["name"]),
        ),
        verilator = verilator_params(
            timeout = "eternal",
            binaries = {":rom_e2e_keymgr_init_test": "firmware"},
            otp = ":otp_img_keymgr_{}".format(config["name"]),
            rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
        ),
    )
    for config in rom_e2e_keymgr_init_configs
]

test_suite(
    name = "keymgr_init",
    tags = ["manual"],
    tests = ["rom_e2e_keymgr_init_{}".format(
        config["name"],
    ) for config in rom_e2e_keymgr_init_configs],
)
