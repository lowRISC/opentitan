# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_image",
    "otp_json",
    "otp_partition",
)
load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

otp_json(
    name = "otp_json_flash_data_cfg_default_unprovisioned",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                # Enable flash data page scrambling and ECC.
                "CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG": "0000090606",
            },
        ),
    ],
)

otp_image(
    name = "otp_img_boot_policy_flash_ecc_error",
    src = "//hw/ip/otp_ctrl/data:otp_json_prod",
    overlays = STD_OTP_OVERLAYS + [":otp_json_flash_data_cfg_default_unprovisioned"],
    visibility = ["//visibility:private"],
)

opentitan_test(
    name = "boot_policy_flash_ecc_error",
    srcs = ["flash_ecc_error_test.c"],
    cw310 = cw310_params(
        changes_otp = True,
        otp = ":otp_img_boot_policy_flash_ecc_error",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
    },
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_c_regs",
        "//hw/top_earlgrey/ip_autogen/flash_ctrl/data:flash_ctrl_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/base:chip",
    ],
)
