# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_image",
    "otp_json",
    "otp_partition",
)
load("//rules:splice.bzl", "bitstream_splice")

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
    ],
    visibility = ["//visibility:private"],
)

otp_image(
    name = "otp_img_secret2_locked_rma",
    src = "//hw/ip/otp_ctrl/data:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [
        ":otp_json_secret2_locked",
    ],
    visibility = ["//visibility:private"],
)

bitstream_splice(
    name = "bitstream_secret2_locked",
    src = "//hw/bitstream/hyperdebug:rom_with_fake_keys",
    data = ":otp_img_secret2_locked_rma",
    meminfo = "//hw/bitstream/hyperdebug:otp_mmi",
    update_usr_access = True,
)
