# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
    "cw310_params",
    "fpga_params",
    "opentitan_test",
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
    "//sw/device/silicon_creator/rom/e2e:defs.bzl",
    "MSG_TEMPLATE_BFV",
    "SLOTS",
    "msg_template_bfv_all_except",
)

package(default_visibility = ["//visibility:public"])

BOOT_POLICY_ROLLBACK_CASES = [
    {
        "a": 0,
        "b": 0,
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.BOOT_POLICY.ROLLBACK)),
        # By default the failure message include BFV but this will conflict with what we're looking for.
        "exit_failure": msg_template_bfv_all_except(CONST.BFV.BOOT_POLICY.ROLLBACK),
    },
    {
        "a": 0,
        "b": 1,
        "exit_success": "slot=0x20080000, security_version=1",
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    {
        "a": 2,
        "b": 0,
        "exit_success": "slot=0x20000000, security_version=2",
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    {
        "a": 1,
        "b": 1,
        "exit_success": "slot=0x20000000, security_version=1",
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
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

[
    otp_image(
        name = "otp_img_boot_policy_rollback_{}".format(lc_state),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS + [":otp_json_boot_policy_rollback"],
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
]

[
    opentitan_test(
        name = "boot_policy_rollback_{}_a_{}_b_{}".format(
            lc_state,
            t["a"],
            t["b"],
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        },
        fpga = fpga_params(
            assemble = "{fw_a}@{slot_a} {fw_b}@{slot_b}",
            binaries = {
                "//sw/device/silicon_creator/rom/e2e/boot_policy_newer:empty_test_slot_a_sec_ver_{}".format(t["a"]): "fw_a",
                "//sw/device/silicon_creator/rom/e2e/boot_policy_newer:empty_test_slot_b_sec_ver_{}".format(t["b"]): "fw_b",
            },
            exit_failure = t["exit_failure"],
            exit_success = t["exit_success"],
            otp = ":otp_img_boot_policy_rollback_{}".format(lc_state),
            slot_a = SLOTS["a"],
            slot_b = SLOTS["b"],
            tags = maybe_skip_in_ci(lc_state_val),
        ),
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
