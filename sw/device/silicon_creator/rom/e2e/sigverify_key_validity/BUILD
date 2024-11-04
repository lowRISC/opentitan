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
    "hex_digits",
)
load(
    "//rules/opentitan:keyutils.bzl",
    "ECDSA_SPX_KEY_STRUCTS",
    "filter_key_structs_for_lc_state",
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
    "//rules:rom_e2e.bzl",
    "maybe_skip_in_ci",
)
load(
    "//sw/device/silicon_creator/rom/e2e:defs.bzl",
    "MSG_PASS",
    "MSG_TEMPLATE_BFV_LCV",
)
load(
    "@bazel_skylib//lib:dicts.bzl",
    "dicts",
)

package(default_visibility = ["//visibility:public"])

# SPHINCS+ is enabled via OTP config in the following lifecycle states.
SPX_OTP_LC_STATES = get_lc_items(
    CONST.LCV.DEV,
    CONST.LCV.PROD,
    CONST.LCV.PROD_END,
    CONST.LCV.RMA,
)

# SPHINCS+ is disabled uncoditionally in these lifecycle states.
SPX_DISABLED_LC_STATES = get_lc_items(
    CONST.LCV.TEST_UNLOCKED0,
    CONST.LCV.TEST_UNLOCKED1,
    CONST.LCV.TEST_UNLOCKED2,
    CONST.LCV.TEST_UNLOCKED3,
    CONST.LCV.TEST_UNLOCKED4,
    CONST.LCV.TEST_UNLOCKED5,
    CONST.LCV.TEST_UNLOCKED6,
    CONST.LCV.TEST_UNLOCKED7,
)

KEY_VALIDITY_TESTS = [
    {
        "name": "ecdsa_revoked",
        "exit_failure": dicts.add(
            {
                lc_state: MSG_PASS
                for lc_state, _ in get_lc_items()
            },
        ),
        "exit_success": dicts.add(
            {
                lc_state: MSG_TEMPLATE_BFV_LCV.format(
                    hex_digits(CONST.BFV.SIGVERIFY.BAD_ECDSA_KEY),
                    hex_digits(lc_state_val),
                )
                for lc_state, lc_state_val in get_lc_items()
            },
        ),
        "ecdsa_state": otp_hex(CONST.SIGVERIFY.KEY_STATE.REVOKED),
        "spx_state": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
    },
    {
        "name": "ecdsa_blank",
        "exit_failure": dicts.add(
            {
                lc_state: MSG_PASS
                for lc_state, _ in get_lc_items()
            },
        ),
        "exit_success": dicts.add(
            {
                lc_state: MSG_TEMPLATE_BFV_LCV.format(
                    hex_digits(CONST.BFV.SIGVERIFY.BAD_ECDSA_KEY),
                    hex_digits(lc_state_val),
                )
                for lc_state, lc_state_val in get_lc_items()
            },
        ),
        "ecdsa_state": otp_hex(CONST.SIGVERIFY.KEY_STATE.BLANK),
        "spx_state": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
    },
    {
        "name": "spx_revoked",
        "exit_failure": dicts.add(
            {
                lc_state: MSG_PASS
                for lc_state, _ in SPX_OTP_LC_STATES
            },
            {
                lc_state: DEFAULT_TEST_FAILURE_MSG
                for lc_state, _ in SPX_DISABLED_LC_STATES
            },
        ),
        "exit_success": dicts.add(
            {
                lc_state: MSG_TEMPLATE_BFV_LCV.format(
                    hex_digits(CONST.BFV.SIGVERIFY.BAD_SPX_KEY),
                    hex_digits(lc_state_val),
                )
                for lc_state, lc_state_val in SPX_OTP_LC_STATES
            },
            {
                lc_state: MSG_PASS
                for lc_state, _ in SPX_DISABLED_LC_STATES
            },
        ),
        "ecdsa_state": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
        "spx_state": otp_hex(CONST.SIGVERIFY.KEY_STATE.REVOKED),
    },
    {
        "name": "spx_blank",
        "exit_failure": dicts.add(
            {
                lc_state: MSG_PASS
                for lc_state, _ in SPX_OTP_LC_STATES
            },
            {
                lc_state: DEFAULT_TEST_FAILURE_MSG
                for lc_state, _ in SPX_DISABLED_LC_STATES
            },
        ),
        "exit_success": dicts.add(
            {
                lc_state: MSG_TEMPLATE_BFV_LCV.format(
                    hex_digits(CONST.BFV.SIGVERIFY.BAD_SPX_KEY),
                    hex_digits(lc_state_val),
                )
                for lc_state, lc_state_val in SPX_OTP_LC_STATES
            },
            {
                lc_state: MSG_PASS
                for lc_state, _ in SPX_DISABLED_LC_STATES
            },
        ),
        "ecdsa_state": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
        "spx_state": otp_hex(CONST.SIGVERIFY.KEY_STATE.BLANK),
    },
]

[
    otp_json(
        name = "otp_json_sigverify_key_validity_{}".format(test["name"]),
        partitions = [
            otp_partition(
                name = "CREATOR_SW_CFG",
                items = {
                    "CREATOR_SW_CFG_SIGVERIFY_SPX_EN": otp_hex(CONST.HARDENED_TRUE),
                },
            ),
            otp_partition(
                name = "ROT_CREATOR_AUTH_STATE",
                items = {
                    "ROT_CREATOR_AUTH_STATE_ECDSA_KEY0": test["ecdsa_state"],
                    "ROT_CREATOR_AUTH_STATE_ECDSA_KEY1": test["ecdsa_state"],
                    "ROT_CREATOR_AUTH_STATE_ECDSA_KEY2": test["ecdsa_state"],
                    "ROT_CREATOR_AUTH_STATE_ECDSA_KEY3": test["ecdsa_state"],
                    "ROT_CREATOR_AUTH_STATE_SPX_KEY0": test["spx_state"],
                    "ROT_CREATOR_AUTH_STATE_SPX_KEY1": test["spx_state"],
                    "ROT_CREATOR_AUTH_STATE_SPX_KEY2": test["spx_state"],
                    "ROT_CREATOR_AUTH_STATE_SPX_KEY3": test["spx_state"],
                },
            ),
        ],
    )
    for test in KEY_VALIDITY_TESTS
]

[
    otp_image(
        name = "otp_img_sigverify_key_validity_{}_{}".format(
            test["name"],
            lc_state,
        ),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS + [
            ":otp_json_sigverify_key_validity_{}".format(test["name"]),
        ],
    )
    for test in KEY_VALIDITY_TESTS
    for lc_state, _ in get_lc_items()
]

[
    opentitan_test(
        name = "sigverify_key_validity_{}_{}_{}_{}".format(
            test["name"],
            lc_state,
            key.ecdsa.name,
            key.spx.name,
        ),
        srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test"],
        ecdsa_key = {key.ecdsa.label: key.ecdsa.name},
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        },
        fpga = fpga_params(
            exit_failure = test["exit_failure"][lc_state],
            exit_success = test["exit_success"][lc_state],
            otp = ":otp_img_sigverify_key_validity_{}_{}".format(
                test["name"],
                lc_state,
            ),
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        spx_key = {key.spx.label: key.spx.name},
        deps = [
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for test in KEY_VALIDITY_TESTS
    for lc_state, lc_state_val in get_lc_items()
    for key in filter_key_structs_for_lc_state(ECDSA_SPX_KEY_STRUCTS, lc_state_val)
]

test_suite(
    name = "rom_e2e_sigverify_key_validity",
    tags = ["manual"],
    tests = [
        "sigverify_key_validity_{}_{}_{}_{}".format(
            test["name"],
            lc_state,
            key.ecdsa.name,
            key.spx.name,
        )
        for test in KEY_VALIDITY_TESTS
        for lc_state, lc_state_val in get_lc_items()
        for key in filter_key_structs_for_lc_state(ECDSA_SPX_KEY_STRUCTS, lc_state_val)
    ],
)
