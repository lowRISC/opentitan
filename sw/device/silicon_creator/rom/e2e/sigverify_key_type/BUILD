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
    "//rules:opentitan.bzl",
    "RSA_ONLY_KEY_STRUCTS",
    "key_allowed_in_lc_state",
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
    "MSG_TEMPLATE_BFV_LCV",
)

package(default_visibility = ["//visibility:public"])

[
    otp_image(
        name = "otp_img_sigverify_key_type_{}".format(lc_state),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS,
    )
    for lc_state, _ in get_lc_items()
]

[
    bitstream_splice(
        name = "bitstream_sigverify_key_type_{}".format(
            lc_state,
        ),
        src = "//hw/bitstream/hyperdebug:rom_with_fake_keys",
        data = ":otp_img_sigverify_key_type_{}".format(
            lc_state,
        ),
        meminfo = "//hw/bitstream/hyperdebug:otp_mmi",
        tags = maybe_skip_in_ci(lc_state_val),
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for lc_state, lc_state_val in get_lc_items()
]

[
    opentitan_functest(
        name = "sigverify_key_type_{}_{}".format(
            lc_state,
            key.rsa.name,
        ),
        cw310 = cw310_params(
            bitstream = ":bitstream_sigverify_key_type_{}".format(lc_state),
            exit_failure = MSG_PASS if not key_allowed_in_lc_state(
                key.rsa,
                lc_state_val,
            ) else MSG_TEMPLATE_BFV_LCV.format(
                hex_digits(CONST.BFV.SIGVERIFY.BAD_RSA_KEY),
                hex_digits(lc_state_val),
            ),
            exit_success = MSG_PASS if key_allowed_in_lc_state(
                key.rsa,
                lc_state_val,
            ) else MSG_TEMPLATE_BFV_LCV.format(
                hex_digits(CONST.BFV.SIGVERIFY.BAD_RSA_KEY),
                hex_digits(lc_state_val),
            ),
            interface = "hyper310",
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        key_struct = key,
        ot_flash_binary = "//sw/device/silicon_creator/rom/e2e:empty_test_slot_a",
        targets = [
            "cw310_rom_with_fake_keys",
        ],
    )
    for lc_state, lc_state_val in get_lc_items()
    for key in RSA_ONLY_KEY_STRUCTS
]

test_suite(
    name = "rom_e2e_sigverify_key_type",
    tags = ["manual"],
    tests = [
        "sigverify_key_type_{}_{}".format(
            lc_state,
            key_name,
        )
        for lc_state, _ in get_lc_items()
        for key_name in [key.rsa.name for key in RSA_ONLY_KEY_STRUCTS]
    ],
)
