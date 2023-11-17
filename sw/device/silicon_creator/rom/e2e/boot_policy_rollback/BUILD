# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan_test.bzl",
    "cw310_params",
    "opentitan_functest",
)
load(
    "//rules:const.bzl",
    "CONST",
    "get_lc_items",
    "hex",
    "hex_digits",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_image",
    "otp_json",
    "otp_partition",
)
load(
    "//rules:rom_e2e.bzl",
    "maybe_skip_in_ci",
)
load(
    "//rules:splice.bzl",
    "bitstream_splice",
)
load(
    "//sw/device/silicon_creator/rom/e2e:defs.bzl",
    "MSG_TEMPLATE_BFV",
)

package(default_visibility = ["//visibility:public"])

BOOT_POLICY_ROLLBACK_CASES = [
    {
        "a": 0,
        "b": 0,
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.BOOT_POLICY.ROLLBACK)),
    },
    {
        "a": 0,
        "b": 1,
        "exit_success": "slot=0x20080000, security_version=1",
    },
    {
        "a": 2,
        "b": 0,
        "exit_success": "slot=0x20000000, security_version=2",
    },
    {
        "a": 1,
        "b": 1,
        "exit_success": "slot=0x20000000, security_version=1",
    },
]

otp_json(
    name = "otp_json_boot_policy_rollback",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                "CREATOR_SW_CFG_MIN_SEC_VER_ROM_EXT": "1",
            },
        ),
    ],
)

[otp_image(
    name = "otp_img_boot_policy_rollback_{}".format(lc_state),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
    overlays = STD_OTP_OVERLAYS + [":otp_json_boot_policy_rollback"],
    visibility = ["//visibility:private"],
) for lc_state, _ in get_lc_items()]

# TODO: Add hyper310 targets?
[bitstream_splice(
    name = "bitstream_boot_policy_rollback_{}".format(
        lc_state,
    ),
    src = "//hw/bitstream:rom_with_fake_keys",
    data = ":otp_img_boot_policy_rollback_{}".format(
        lc_state,
    ),
    meminfo = "//hw/bitstream:otp_mmi",
    update_usr_access = True,
    visibility = ["//visibility:private"],
) for lc_state, _ in get_lc_items()]

[
    opentitan_functest(
        name = "boot_policy_rollback_{}_a_{}_b_{}".format(
            lc_state,
            t["a"],
            t["b"],
        ),
        cw310 = cw310_params(
            bitstream = "bitstream_boot_policy_rollback_{}".format(lc_state),
            exit_success = t["exit_success"],
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        key_struct = "multislot",
        ot_flash_binary = "//sw/device/silicon_creator/rom/e2e/boot_policy_newer:sec_ver_{}_{}_image".format(
            t["a"],
            t["b"],
        ),
        targets = ["cw310_rom_with_fake_keys"],
    )
    for lc_state, lc_state_val in get_lc_items()
    for t in BOOT_POLICY_ROLLBACK_CASES
]

test_suite(
    name = "rom_e2e_boot_policy_rollback",
    tags = ["manual"],
    tests = [
        "boot_policy_rollback_{}_a_{}_b_{}".format(
            lc_state,
            t["a"],
            t["b"],
        )
        for lc_state, _ in get_lc_items()
        for t in BOOT_POLICY_ROLLBACK_CASES
    ],
)
