# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "DEFAULT_TEST_SUCCESS_MSG",
    "cw310_params",
    "hyper310_params",
    "opentitan_test",
    "rsa_key_for_lc_state",
)
load(
    "//rules:const.bzl",
    "CONST",
    "get_lc_items",
    "hex",
    "hex_digits",
    "lcv_hw_to_sw",
)
load(
    "//rules:opentitan.bzl",
    "RSA_ONLY_KEY_STRUCTS",
)
load(
    "//rules:manifest.bzl",
    "manifest",
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
    "@bazel_skylib//lib:structs.bzl",
    "structs",
)
load(
    "//sw/device/silicon_creator/rom/e2e:defs.bzl",
    "MSG_TEMPLATE_BFV",
)

package(default_visibility = ["//visibility:public"])

# Sigverify usage constraint tests
_test_device_id = [
    "0xa0a1a2a3",  # Least-significant word
    "0x12345678",
    "0x00000003",
    "0xabababab",
    "0xcdcdcdcd",
    "0x01010101",
    "0x10101010",
    "0xf0f1f2f3",  # Most-significant word
]

_test_manuf_states = {
    "creator": "0xfedcba98",
    "owner": "0x12345678",
}

# Generate OTP image with a specific device ID, creator manufacturing state,
# and owner manufacturing state
_test_device_id_joined = "0x" + "".join([word[2:] for word in reversed(_test_device_id)])

otp_json(
    name = "otp_json_set_usage_constraint_params_overlay",
    partitions = [
        otp_partition(
            name = "HW_CFG",
            items = {"DEVICE_ID": _test_device_id_joined},
        ),
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {"CREATOR_SW_CFG_MANUF_STATE": _test_manuf_states["creator"]},
        ),
        otp_partition(
            name = "OWNER_SW_CFG",
            items = {"OWNER_SW_CFG_MANUF_STATE": _test_manuf_states["owner"]},
        ),
    ],
    visibility = ["//visibility:private"],
)

[
    otp_image(
        name = "otp_img_sigverify_usage_constraints_{}".format(lc_state),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS + [":otp_json_set_usage_constraint_params_overlay"],
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
]

_SIGVERIFY_FAIL_MSG = MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.SIGVERIFY.BAD_RSA_SIGNATURE))

device_id_test_cases = [
    {
        "name": "device_id_match",
        "manifest": {
            "selector_bits": "0xff",
            "device_id": _test_device_id,
        },
        "otp": ":otp_img_sigverify_usage_constraints_rma",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": _SIGVERIFY_FAIL_MSG,
        "lc_state_val": CONST.LCV.RMA,
    },
    {
        "name": "device_id_no_match",
        "manifest": {
            "selector_bits": "0xff",
            "device_id": ["0xbad"] * 8,
        },
        "otp": ":otp_img_sigverify_usage_constraints_rma",
        "exit_success": _SIGVERIFY_FAIL_MSG,
        "exit_failure": DEFAULT_TEST_SUCCESS_MSG,
        "lc_state_val": CONST.LCV.RMA,
    },
    {
        "name": "device_id_family_match",
        "manifest": {
            # Select words 0, 3, and 5 to match on:
            # 0b0010_1001 = 0x29
            "selector_bits": "0x29",
            "device_id": [
                _test_device_id[0],
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
                _test_device_id[3],
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
                _test_device_id[5],
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
            ],
        },
        "otp": ":otp_img_sigverify_usage_constraints_rma",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": _SIGVERIFY_FAIL_MSG,
        "lc_state_val": CONST.LCV.RMA,
    },
    {
        "name": "device_id_family_no_match",
        "manifest": {
            # Select words 0, 3, and 5 to match on:
            # 0b0010_1001 = 0x29
            "selector_bits": "0x29",
            "device_id": [
                "0xbad",
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
                "0xbad",
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
                "0xbad",
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
            ],
        },
        "otp": ":otp_img_sigverify_usage_constraints_rma",
        "exit_success": _SIGVERIFY_FAIL_MSG,
        "exit_failure": DEFAULT_TEST_SUCCESS_MSG,
        "lc_state_val": CONST.LCV.RMA,
    },
]

lc_state_test_cases = [
    {
        "name": "lc_state_{}_{}".format(
            lc_state,
            "match" if match_case else "no_match",
        ),
        # Note: the manifest value for a given life-cycle state is determined
        # by CONST.LCV_SW instead of CONST.LCV. These two structs have slightly
        # different mappings for the TEST_* LC state, so lc_hw_to_sw is used to
        # convert from the names in CONST.LCV to those in CONST.LCV_SW before
        # performing the lookup.
        "manifest": {
            "selector_bits": "0x400",
            "life_cycle_state": hex(lcv_hw_to_sw(lc_state_val)) if match_case else "0",
        },
        "otp": ":otp_img_sigverify_usage_constraints_{}".format(lc_state),
        "exit_success": DEFAULT_TEST_SUCCESS_MSG if match_case else _SIGVERIFY_FAIL_MSG,
        "exit_failure": _SIGVERIFY_FAIL_MSG if match_case else DEFAULT_TEST_SUCCESS_MSG,
        "lc_state_val": lc_state_val,
    }
    for lc_state, lc_state_val in get_lc_items()
    for match_case in (True, False)
]

manuf_state_test_cases = [
    {
        "name": "manuf_state_{}_{}".format(
            entity,
            "match" if match_case else "no_match",
        ),
        "manifest": {
            "selector_bits": "0x100" if entity == "creator" else "0x200",
            "manuf_state_{}".format(entity): "{}".format(_test_manuf_states[entity]) if match_case else "0",
        },
        "otp": ":otp_img_sigverify_usage_constraints_rma",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG if match_case else _SIGVERIFY_FAIL_MSG,
        "exit_failure": _SIGVERIFY_FAIL_MSG if match_case else DEFAULT_TEST_SUCCESS_MSG,
        "lc_state_val": CONST.LCV.RMA,
    }
    for entity in ("creator", "owner")
    for match_case in (True, False)
]

# The all-constraints case is tested against all LC states. For each LC state,
# we try all 5 LC state settings in the manifest and ensure that only one
# boots successfully.
all_constr_test_cases = [
    {
        "name": "all_constraints_mf_lc_{}_bs_lc_{}".format(
            mf_lc_state.lower(),
            bs_lc_state,
        ),
        "manifest": {
            "selector_bits": "0x7ff",
            "device_id": _test_device_id,
            "life_cycle_state": hex(mf_lc_val),
            "manuf_state_creator": _test_manuf_states["creator"],
            "manuf_state_owner": _test_manuf_states["owner"],
        },
        "otp": ":otp_img_sigverify_usage_constraints_{}".format(bs_lc_state),
        "exit_success": DEFAULT_TEST_SUCCESS_MSG if mf_lc_val == lcv_hw_to_sw(bs_lc_val) else _SIGVERIFY_FAIL_MSG,
        "exit_failure": _SIGVERIFY_FAIL_MSG if mf_lc_val == lcv_hw_to_sw(bs_lc_val) else DEFAULT_TEST_SUCCESS_MSG,
        "lc_state_val": bs_lc_val,
    }
    for mf_lc_state, mf_lc_val in structs.to_dict(CONST.LCV_SW).items()
    for bs_lc_state, bs_lc_val in get_lc_items()
]

# Usage constraints that are not selected by the selector_bits must be set to
# MANIFEST_USAGE_CONSTRAINT_UNSELECTED_WORD. These tests check for a failure if
# they are not by setting various fields to otherwise valid values while
# setting the selector_bits to 0.
invalid_unselected_word_cases = [
    {
        "name": "invalid_unselected_{}".format(field),
        "manifest": {
            field: field_val,
            "selector_bits": "0",
            "selector_mismatch_is_failure": False,
        },
        "otp": ":otp_img_sigverify_usage_constraints_rma",
        "exit_success": _SIGVERIFY_FAIL_MSG,
        "exit_failure": DEFAULT_TEST_SUCCESS_MSG,
        "lc_state_val": CONST.LCV.RMA,
    }
    for field, field_val in [
        ("device_id", _test_device_id),
        (
            "life_cycle_state",
            hex(CONST.LCV_SW.RMA),
        ),
        (
            "manuf_state_creator",
            _test_manuf_states["creator"],
        ),
        (
            "manuf_state_owner",
            _test_manuf_states["owner"],
        ),
    ]
]

test_cases = device_id_test_cases + lc_state_test_cases + manuf_state_test_cases + all_constr_test_cases + invalid_unselected_word_cases

[
    opentitan_test(
        name = "sigverify_usage_constraint_{}".format(t["name"]),
        srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test"],
        cw310 = cw310_params(
            exit_failure = t["exit_failure"],
            exit_success = t["exit_success"],
            otp = t["otp"],
            tags = maybe_skip_in_ci(t["lc_state_val"]),
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
        },
        hyper310 = hyper310_params(
            exit_failure = t["exit_failure"],
            exit_success = t["exit_success"],
            otp = t["otp"],
            tags = maybe_skip_in_ci(t["lc_state_val"]),
        ),
        manifest = manifest(
            dict(
                t["manifest"],
                name = "sigverify_usage_constraint_manifest_{}".format(t["name"]),
                address_translation = hex(CONST.HARDENED_FALSE),
                identifier = hex(CONST.ROM_EXT),
            ),
        ),
        rsa_key = rsa_key_for_lc_state(
            RSA_ONLY_KEY_STRUCTS,
            t["lc_state_val"],
        ),
        deps = [
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:otp",
            "//sw/device/silicon_creator/lib/sigverify:spx_verify",
        ],
    )
    for t in test_cases
]

test_suite(
    name = "rom_e2e_sigverify_usage_constraints",
    tags = ["manual"],
    tests = ["sigverify_usage_constraint_{}".format(t["name"]) for t in test_cases],
)
