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
    "//sw/device/silicon_creator/rom_ext/e2e:defs.bzl",
    "DEVICE_ID",
)

package(default_visibility = ["//visibility:public"])

otp_json(
    name = "otp_json_secret2_locked",
    partitions = [
        otp_partition(
            name = "SECRET2",
            items = {
                # We aren't testing keymgr for ROM_EXT tests and we want
                # reproducible bitstreams for all tests.
                "RMA_TOKEN": "0000000000000005",
                "CREATOR_ROOT_KEY_SHARE0": "1111111111111111111111111111111111111111111111111111111111111111",
                "CREATOR_ROOT_KEY_SHARE1": "2222222222222222222222222222222222222222222222222222222222222222",
            },
            lock = True,
        ),
        otp_partition(
            name = "HW_CFG0",
            items = {
                "DEVICE_ID": DEVICE_ID,
            },
            lock = True,
        ),
    ],
)

otp_image(
    name = "otp_img_secret2_locked_rma",
    src = "//hw/top_earlgrey/data/otp:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [
        ":otp_json_secret2_locked",
    ],
)

otp_json(
    name = "otp_json_reset_reason",
    partitions = [
        otp_partition(
            name = "OWNER_SW_CFG",
            items = {
                "OWNER_SW_CFG_ROM_PRESERVE_RESET_REASON_EN": otp_hex(CONST.HARDENED_TRUE),
                "OWNER_SW_CFG_ROM_WATCHDOG_BITE_THRESHOLD_CYCLES": otp_hex(200000),
            },
        ),
    ],
)

otp_image(
    name = "otp_img_secret2_locked_preserve_reset_prod",
    src = "//hw/top_earlgrey/data/otp:otp_json_prod",
    overlays = STD_OTP_OVERLAYS + [
        ":otp_json_secret2_locked",
        ":otp_json_reset_reason",
    ],
)
