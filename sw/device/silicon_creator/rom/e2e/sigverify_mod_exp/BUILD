# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "opentitan_test",
    "rsa_key_for_lc_state",
)
load(
    "//rules:opentitan.bzl",
    "RSA_ONLY_KEY_STRUCTS",
)
load(
    "//rules:const.bzl",
    "CONST",
    "get_lc_items",
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
    "//rules:splice.bzl",
    "bitstream_splice",
)

package(default_visibility = ["//visibility:public"])

SIGVERIFY_MOD_EXP_CASES = [
    {
        "name": "sw",
        "use_sw_rsa_verify": CONST.HARDENED_TRUE,
        "exit_success": {lc_state: "use_sw_rsa_verify=0x00000739" for lc_state, _ in get_lc_items()},
    },
    {
        "name": "otbn",
        "use_sw_rsa_verify": CONST.HARDENED_FALSE,
        "exit_success": {lc_state: "use_sw_rsa_verify=0x000001d4" for lc_state, _ in get_lc_items()},
    },
    {
        "name": "invalid",
        "use_sw_rsa_verify": 0,
        "exit_success": {lc_state: "use_sw_rsa_verify=0x00000000" for lc_state, lc_state_val in get_lc_items()},
    },
]

[
    otp_json(
        name = "otp_json_sigverify_mod_exp_{}".format(t["name"]),
        partitions = [
            otp_partition(
                name = "CREATOR_SW_CFG",
                items = {"CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN": otp_hex(t["use_sw_rsa_verify"])},
            ),
        ],
    )
    for t in SIGVERIFY_MOD_EXP_CASES
]

[
    otp_image(
        name = "otp_img_sigverify_mod_exp_{}_{}".format(
            lc_state,
            t["name"],
        ),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS + [":otp_json_sigverify_mod_exp_{}".format(t["name"])],
    )
    for lc_state, _ in get_lc_items()
    for t in SIGVERIFY_MOD_EXP_CASES
]

[
    bitstream_splice(
        name = "bitstream_sigverify_mod_exp_{}_{}".format(
            lc_state,
            t["name"],
        ),
        src = "//hw/bitstream/hyperdebug:rom_with_fake_keys",
        data = ":otp_img_sigverify_mod_exp_{}_{}".format(
            lc_state,
            t["name"],
        ),
        meminfo = "//hw/bitstream/hyperdebug:otp_mmi",
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
    for t in SIGVERIFY_MOD_EXP_CASES
]

[
    opentitan_test(
        name = "sigverify_mod_exp_{}_{}".format(
            lc_state,
            t["name"],
        ),
        srcs = ["sigverify_mod_exp.c"],
        cw310 = cw310_params(
            bitstream = ":bitstream_sigverify_mod_exp_{}_{}".format(
                lc_state,
                t["name"],
            ),
            exit_success = t["exit_success"][lc_state],
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        },
        manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
        rsa_key = rsa_key_for_lc_state(
            RSA_ONLY_KEY_STRUCTS,
            lc_state_val,
        ),
        deps = [
            "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
            "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:lifecycle",
            "//sw/device/silicon_creator/lib/drivers:otp",
            "//sw/device/silicon_creator/lib/sigverify:spx_verify",
        ],
    )
    for lc_state, lc_state_val in get_lc_items()
    for t in SIGVERIFY_MOD_EXP_CASES
]

test_suite(
    name = "rom_e2e_sigverify_mod_exp",
    tags = ["manual"],
    tests = [
        "sigverify_mod_exp_{}_{}".format(
            lc_state,
            t["name"],
        )
        for lc_state, _ in get_lc_items()
        for t in SIGVERIFY_MOD_EXP_CASES
    ],
)
