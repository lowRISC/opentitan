# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan_test.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
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
    "//rules:opentitan.bzl",
    "RSA_ONLY_KEY_STRUCTS",
    "bin_to_vmem",
    "opentitan_multislot_flash_binary",
    "scramble_flash_vmem",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_image",
    "otp_json",
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
    "MSG_PASS",
    "MSG_TEMPLATE_BFV",
    "SIGVERIFY_LC_KEYS",
    "SLOTS",
)

package(default_visibility = ["//visibility:public"])

BOOT_POLICY_VALID_CASES = [
    {
        "desc": "good",
        "suffix": "",
    },
    {
        "desc": "bad",
        "suffix": "_corrupted",
    },
]

[
    opentitan_multislot_flash_binary(
        name = "boot_policy_valid_img_a_{}_b_{}".format(
            a["desc"],
            b["desc"],
        ),
        testonly = True,
        srcs = {
            "//sw/device/silicon_creator/rom/e2e:empty_test_slot_a{}".format(a["suffix"]): {
                "key": RSA_ONLY_KEY_STRUCTS[2],
                "offset": SLOTS["a"],
            },
            "//sw/device/silicon_creator/rom/e2e:empty_test_slot_b{}".format(b["suffix"]): {
                "key": RSA_ONLY_KEY_STRUCTS[2],
                "offset": SLOTS["b"],
            },
        },
        devices = ["fpga_cw310"],
    )
    for a in BOOT_POLICY_VALID_CASES
    for b in BOOT_POLICY_VALID_CASES
]

[
    otp_image(
        name = "otp_img_boot_policy_valid_{}".format(lc_state),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS,
    )
    for lc_state, _ in get_lc_items()
]

# Splice OTP images into bitstreams
[
    bitstream_splice(
        name = "bitstream_boot_policy_valid_{}".format(lc_state),
        src = "//hw/bitstream/hyperdebug:rom_with_fake_keys",
        data = ":otp_img_boot_policy_valid_{}".format(lc_state),
        meminfo = "//hw/bitstream/hyperdebug:otp_mmi",
        update_usr_access = True,
    )
    for lc_state, _ in get_lc_items()
]

[
    opentitan_functest(
        name = "boot_policy_valid_{}_a_{}_b_{}".format(
            lc_state,
            a["desc"],
            b["desc"],
        ),
        cw310 = cw310_params(
            bitstream = "bitstream_boot_policy_valid_{}".format(lc_state),
            exit_failure = MSG_PASS if a["desc"] == b["desc"] and a["desc"] == "bad" else DEFAULT_TEST_FAILURE_MSG,
            exit_success = MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.SIGVERIFY.BAD_RSA_SIGNATURE)) if a["desc"] == b["desc"] and a["desc"] == "bad" else MSG_PASS,
            interface = "hyper310",
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        key_struct = "multislot",
        ot_flash_binary = ":boot_policy_valid_img_a_{}_b_{}".format(
            a["desc"],
            b["desc"],
        ),
        targets = ["cw310_rom_with_fake_keys"],
    )
    for lc_state, lc_state_val in get_lc_items()
    for a in BOOT_POLICY_VALID_CASES
    for b in BOOT_POLICY_VALID_CASES
]

test_suite(
    name = "rom_e2e_boot_policy_valid",
    tags = ["manual"],
    tests = [
        "boot_policy_valid_{}_a_{}_b_{}".format(
            lc_state,
            a["desc"],
            b["desc"],
        )
        for lc_state, _ in get_lc_items()
        for a in BOOT_POLICY_VALID_CASES
        for b in BOOT_POLICY_VALID_CASES
    ],
)
