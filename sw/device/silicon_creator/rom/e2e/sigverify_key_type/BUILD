# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST", "get_lc_items")
load("//rules/opentitan:keyutils.bzl", "ECDSA_SPX_KEY_STRUCTS")
load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "fpga_params",
    "opentitan_test",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_hex",
    "otp_image",
    "otp_json",
    "otp_partition",
)
load("//rules:rom_e2e.bzl", "maybe_skip_in_ci")
load("@bazel_skylib//lib:dicts.bzl", "dicts")
load(
    ":key_type.bzl",
    "ecdsa_exit_failure",
    "ecdsa_exit_success",
    "spx_exit_failure",
    "spx_exit_success",
)

package(default_visibility = ["//visibility:public"])

# Expected exit signatures for ECDSA keys against different LC states.
ECDSA_ALLOWED_IN_LC_STATES = {
    "exit_failure": dicts.add(
        {
            key.ecdsa.name: dicts.add(
                {
                    lc_state: ecdsa_exit_failure(lc_state_val, key)
                    for lc_state, lc_state_val in get_lc_items()
                },
            )
            for key in ECDSA_SPX_KEY_STRUCTS
        },
    ),
    "exit_success": dicts.add(
        {
            key.ecdsa.name: dicts.add(
                {
                    lc_state: ecdsa_exit_success(lc_state_val, key)
                    for lc_state, lc_state_val in get_lc_items()
                },
            )
            for key in ECDSA_SPX_KEY_STRUCTS
        },
    ),
}

# Expected exit signatures for SPX keys against different LC states.
SPX_ALLOWED_IN_LC_STATES = {
    "exit_failure": dicts.add(
        {
            key.spx.name: dicts.add(
                {
                    lc_state: spx_exit_failure(lc_state_val, key)
                    for lc_state, lc_state_val in get_lc_items()
                },
            )
            for key in ECDSA_SPX_KEY_STRUCTS
        },
    ),
    "exit_success": dicts.add(
        {
            key.spx.name: dicts.add(
                {
                    lc_state: spx_exit_success(lc_state_val, key)
                    for lc_state, lc_state_val in get_lc_items()
                },
            )
            for key in ECDSA_SPX_KEY_STRUCTS
        },
    ),
}

# ECDSA key type tests. All tests use a PROD SPX key which is valid across all
# LC states.
KEY_TYPE_ECDSA_TESTS = [
    {
        "name": key.ecdsa.name,
        "exit_failure": ECDSA_ALLOWED_IN_LC_STATES["exit_failure"][key.ecdsa.name],
        "exit_success": ECDSA_ALLOWED_IN_LC_STATES["exit_success"][key.ecdsa.name],
        "ecdsa_key": {key.ecdsa.label: key.ecdsa.name},
        "spx_key": {"//sw/device/silicon_creator/rom/keys/fake/spx:prod_key_0_spx": "prod_key_0_spx"},
    }
    for key in ECDSA_SPX_KEY_STRUCTS
]

# SPX key type tests. All tests use a PROD ECDSA key which is valid across all
# LC states.
KEY_TYPE_SPX_TESTS = [
    {
        "name": key.spx.name,
        "exit_failure": SPX_ALLOWED_IN_LC_STATES["exit_failure"][key.spx.name],
        "exit_success": SPX_ALLOWED_IN_LC_STATES["exit_success"][key.spx.name],
        "ecdsa_key": {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
        "spx_key": {key.spx.label: key.spx.name},
    }
    for key in ECDSA_SPX_KEY_STRUCTS
]

KEY_TYPE_TESTS = KEY_TYPE_ECDSA_TESTS + KEY_TYPE_SPX_TESTS

otp_json(
    name = "otp_json_enable_spx",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                "CREATOR_SW_CFG_SIGVERIFY_SPX_EN": otp_hex(CONST.HARDENED_TRUE),
            },
        ),
    ],
)

[
    otp_image(
        name = "otp_img_sigverify_key_type_{}".format(lc_state),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS + [
            ":otp_json_enable_spx",
        ],
    )
    for lc_state, _ in get_lc_items()
]

[
    opentitan_test(
        name = "sigverify_key_type_{}_{}".format(
            lc_state,
            test["name"],
        ),
        srcs = [
            "//sw/device/silicon_creator/rom/e2e:empty_test",
        ],
        ecdsa_key = test["ecdsa_key"],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        },
        fpga = fpga_params(
            exit_failure = test["exit_failure"][lc_state],
            exit_success = test["exit_success"][lc_state],
            otp = "otp_img_sigverify_key_type_{}".format(lc_state),
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        spx_key = test["spx_key"],
        deps = [
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:otp",
            "//sw/device/silicon_creator/lib/sigverify:spx_verify",
        ],
    )
    for test in KEY_TYPE_TESTS
    for lc_state, lc_state_val in get_lc_items()
]

test_suite(
    name = "rom_e2e_sigverify_key_type",
    tags = ["manual"],
    tests = [
        "sigverify_key_type_{}_{}".format(
            lc_state,
            test["name"],
        )
        for test in KEY_TYPE_TESTS
        for lc_state, _ in get_lc_items()
    ],
)
