# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan_test.bzl",
    "cw310_params",
    "dv_params",
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
    "filter_key_structs_for_lc_state",
    "opentitan_multislot_flash_binary",
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
    "SIGVERIFY_LC_KEYS",
    "SLOTS",
)

package(default_visibility = ["//visibility:public"])

[
    opentitan_multislot_flash_binary(
        name = "sigverify_always_img_a_{}_b_{}_{}".format(
            "nothing" if slot == "b" else "bad",
            "nothing" if slot == "a" else "bad",
            key,
        ),
        testonly = True,
        srcs = {
            "//sw/device/silicon_creator/rom/e2e:empty_test_slot_{}_corrupted".format(slot): {
                "key": key,
                "offset": offset,
            },
        },
        devices = [
            "sim_dv",
            "fpga_cw310",
        ],
    )
    for slot, offset in SLOTS.items()
    for key in SIGVERIFY_LC_KEYS
]

[
    opentitan_multislot_flash_binary(
        name = "sigverify_always_img_a_bad_b_bad_{}".format(key),
        testonly = True,
        srcs = {
            "//sw/device/silicon_creator/rom/e2e:empty_test_slot_a_corrupted": {
                "key": key,
                "offset": SLOTS["a"],
            },
            "//sw/device/silicon_creator/rom/e2e:empty_test_slot_b_corrupted": {
                "key": key,
                "offset": SLOTS["b"],
            },
        },
        devices = [
            "sim_dv",
            "fpga_cw310",
        ],
    )
    for key in SIGVERIFY_LC_KEYS
]

# Since we cannot feed the `assemble_flash_image` rule that is instantiated by
# the `opentitan_multislot_flash_binary` macro an empty dictionary, we create
# two images with "nothing" in them by created files of all ones, and stitching
# them together.
[
    genrule(
        name = "sigverify_always_img_{}_nothing_{}_bin_signed_{}".format(slot, device, key),
        outs = ["sigverify_always_img_{}_all_ones_{}_bin_signed_{}".format(slot, device, key)],
        cmd_bash = "touch $(OUTS)",
    )
    for slot in SLOTS
    for device in [
        "sim_dv",
        "fpga_cw310",
    ]
    for key in SIGVERIFY_LC_KEYS
]

[
    opentitan_multislot_flash_binary(
        name = "sigverify_always_img_a_nothing_b_nothing_{}".format(key),
        testonly = True,
        srcs = {
            ":sigverify_always_img_a_nothing": {
                "key": key,
                "offset": SLOTS["a"],
            },
            ":sigverify_always_img_b_nothing": {
                "key": key,
                "offset": SLOTS["b"],
            },
        },
        devices = [
            "sim_dv",
            "fpga_cw310",
        ],
    )
    for key in SIGVERIFY_LC_KEYS
]

[otp_image(
    name = "otp_img_sigverify_always_{}".format(lc_state),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
    overlays = STD_OTP_OVERLAYS,
) for lc_state, _ in get_lc_items()]

# Splice OTP images into bitstreams
[
    bitstream_splice(
        name = "bitstream_sigverify_always_{}".format(lc_state),
        src = "//hw/bitstream/hyperdebug:rom_with_fake_keys",
        data = ":otp_img_sigverify_always_{}".format(lc_state),
        meminfo = "//hw/bitstream/hyperdebug:otp_mmi",
        tags = maybe_skip_in_ci(lc_state_val),
        update_usr_access = True,
    )
    for lc_state, lc_state_val in get_lc_items()
]

SIGVERIFY_BAD_CASES = [
    {
        "a": "nothing",
        "b": "bad",
        "expected_bfv": hex_digits(CONST.BFV.SIGVERIFY.BAD_RSA_SIGNATURE),
    },
    {
        "a": "bad",
        "b": "nothing",
        "expected_bfv": hex_digits(CONST.BFV.SIGVERIFY.BAD_RSA_SIGNATURE),
    },
    {
        "a": "bad",
        "b": "bad",
        "expected_bfv": hex_digits(CONST.BFV.SIGVERIFY.BAD_RSA_SIGNATURE),
    },
    {
        "a": "nothing",
        "b": "nothing",
        "expected_bfv": hex_digits(CONST.BFV.BOOT_POLICY.BAD_IDENTIFIER),
    },
]

[
    opentitan_functest(
        name = "sigverify_always_{}_a_{}_b_{}".format(
            lc_state,
            case["a"],
            case["b"],
        ),
        cw310 = cw310_params(
            bitstream = ":bitstream_sigverify_always_{}".format(lc_state),
            exit_failure = MSG_PASS,
            exit_success = MSG_TEMPLATE_BFV_LCV.format(
                case["expected_bfv"],
                hex_digits(lc_state_val),
            ),
            interface = "hyper310",
            otp = ":otp_img_sigverify_always_{}".format(lc_state),
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        dv = dv_params(
            otp = ":otp_img_sigverify_always_{}".format(lc_state),
            rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
        ),
        key_struct = "multislot",
        ot_flash_binary = ":sigverify_always_img_a_{}_b_{}_{}".format(
            case["a"],
            case["b"],
            filter_key_structs_for_lc_state(RSA_ONLY_KEY_STRUCTS, lc_state_val)[0].rsa.name,
        ),
        targets = [
            "dv",
            "cw310_rom_with_fake_keys",
        ],
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
