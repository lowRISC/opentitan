# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "fpga_params",
    "opentitan_test",
)
load(
    "//rules:const.bzl",
    "CONST",
    "get_lc_items",
    "hex_digits",
)
load(
    "//rules/opentitan:keyutils.bzl",
    "ECDSA_ONLY_KEY_STRUCTS",
    "filter_key_structs_for_lc_state",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_image",
)
load(
    "//rules:rom_e2e.bzl",
    "maybe_skip_in_ci",
)
load(
    "//sw/device/silicon_creator/rom/e2e:defs.bzl",
    "MSG_PASS",
    "MSG_TEMPLATE_BFV_LCV",
    "SLOTS",
)

package(default_visibility = ["//visibility:public"])

[otp_image(
    name = "otp_img_sigverify_always_{}".format(lc_state),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
    overlays = STD_OTP_OVERLAYS,
) for lc_state, _ in get_lc_items()]

SIGVERIFY_BAD_CASES = [
    {
        "a": "nothing",
        "b": "bad",
        "expected_bfv": hex_digits(CONST.BFV.SIGVERIFY.BAD_ECDSA_SIGNATURE),
    },
    {
        "a": "bad",
        "b": "nothing",
        "expected_bfv": hex_digits(CONST.BFV.SIGVERIFY.BAD_ECDSA_SIGNATURE),
    },
    {
        "a": "bad",
        "b": "bad",
        "expected_bfv": hex_digits(CONST.BFV.SIGVERIFY.BAD_ECDSA_SIGNATURE),
    },
    {
        "a": "nothing",
        "b": "nothing",
        "expected_bfv": hex_digits(CONST.BFV.BOOT_POLICY.BAD_IDENTIFIER),
    },
]

[
    opentitan_test(
        name = "sigverify_always_{}_a_{}_b_{}".format(
            lc_state,
            case["a"],
            case["b"],
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        },
        fpga = fpga_params(
            assemble = " ".join([
                "{{slot_{}}}@{}".format(slot, addr)
                for (slot, addr) in SLOTS.items()
                if case[slot] == "bad"
            ]),
            binaries = {
                "//sw/device/silicon_creator/rom/e2e:empty_test_slot_{}_{}_corrupted_fpga_cw310_rom_with_fake_keys_signed_bin"
                    .format(
                    slot,
                    filter_key_structs_for_lc_state(ECDSA_ONLY_KEY_STRUCTS, lc_state_val)[0].ecdsa.name,
                ): "slot_{}".format(slot)
                for (slot, addr) in SLOTS.items()
                if case[slot] == "bad"
            },
            exit_failure = MSG_PASS,
            exit_success = MSG_TEMPLATE_BFV_LCV.format(
                case["expected_bfv"],
                hex_digits(lc_state_val),
            ),
            otp = ":otp_img_sigverify_always_{}".format(lc_state),
            tags = maybe_skip_in_ci(lc_state_val),
        ),
    )
    for case in SIGVERIFY_BAD_CASES
    for lc_state, lc_state_val in get_lc_items()
]

test_suite(
    name = "sigverify_always",
    tags = ["manual"],
    tests = [
        "sigverify_always_{}_a_{}_b_{}".format(
            lc_state,
            case["a"],
            case["b"],
        )
        for case in SIGVERIFY_BAD_CASES
        for lc_state, _ in get_lc_items()
    ],
)
