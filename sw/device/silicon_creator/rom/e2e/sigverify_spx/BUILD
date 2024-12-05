# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "ecdsa_key_for_lc_state",
    "fpga_params",
    "opentitan_binary",
    "opentitan_test",
    "spx_key_for_lc_state",
)
load("//rules:const.bzl", "CONST", "get_lc_items")
load("//rules/opentitan:keyutils.bzl", "ECDSA_SPX_KEY_STRUCTS")
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_hex",
    "otp_image",
    "otp_json",
    "otp_partition",
)
load("//rules:rom_e2e.bzl", "maybe_skip_in_ci")
load("//rules:splice.bzl", "bitstream_splice")
load("@bazel_skylib//lib:dicts.bzl", "dicts")

package(default_visibility = ["//visibility:public"])

# We check the OTP item in these lifecycle states.
SPX_OTP_LC_STATES = [
    "prod",
    "prod_end",
    "dev",
    "rma",
]

# SPHINCS+ is disabled uncoditionally in these lifecycle states
SPX_DISABLED_LC_STATES = [
    "test_unlocked0",
    "test_unlocked1",
    "test_unlocked2",
    "test_unlocked3",
    "test_unlocked4",
    "test_unlocked5",
    "test_unlocked6",
    "test_unlocked7",
]

# Any value other than SPX_DISABLED enables SPHINCS+.
SIGVERIFY_SPX_CASES = [
    {
        "name": "enabled_zero",
        "spx_en": 0,
        "exit_success": dicts.add(
            {
                lc_state: "spx_en=0x00000000, spx_en_otp=0x00000000"
                for lc_state in SPX_OTP_LC_STATES
            },
            {
                lc_state: "spx_en=0x8d6c8c17, spx_en_otp=0x00000000"
                for lc_state in SPX_DISABLED_LC_STATES
            },
        ),
    },
    {
        "name": "enabled_true",
        "spx_en": CONST.HARDENED_TRUE,
        "exit_success": dicts.add(
            {
                lc_state: "spx_en=0x00000739, spx_en_otp=0x00000739"
                for lc_state in SPX_OTP_LC_STATES
            },
            {
                lc_state: "spx_en=0x8d6c8c17, spx_en_otp=0x00000739"
                for lc_state in SPX_DISABLED_LC_STATES
            },
        ),
    },
    {
        "name": "disabled",
        "spx_en": CONST.SPX_DISABLED,
        "exit_success": {
            lc_state: "spx_en=0x8d6c8c17, spx_en_otp=0x8d6c8c17"
            for lc_state in SPX_OTP_LC_STATES + SPX_DISABLED_LC_STATES
        },
    },
]

opentitan_binary(
    name = "empty_test_sigverify_spx",
    testonly = True,
    srcs = ["sigverify_spx_test.c"],
    ecdsa_key = ecdsa_key_for_lc_state(
        ECDSA_SPX_KEY_STRUCTS,
        CONST.LCV.RMA,
    ),
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys",
        "//hw/top_earlgrey:sim_dv",
        "//hw/top_earlgrey:sim_verilator",
    ],
    kind = "flash",
    spx_key = spx_key_for_lc_state(
        ECDSA_SPX_KEY_STRUCTS,
        CONST.LCV.RMA,
    ),
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_c_regs",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/sigverify:spx_verify",
    ],
)

[
    otp_json(
        name = "otp_json_sigverify_spx_{}".format(t["name"]),
        partitions = [
            otp_partition(
                name = "CREATOR_SW_CFG",
                items = {
                    "CREATOR_SW_CFG_SIGVERIFY_SPX_EN": otp_hex(t["spx_en"]),
                },
            ),
        ],
    )
    for t in SIGVERIFY_SPX_CASES
]

[
    otp_image(
        name = "otp_img_sigverify_spx_{}_{}".format(
            lc_state,
            t["name"],
        ),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS + [
            ":otp_json_sigverify_spx_{}".format(t["name"]),
        ],
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
    for t in SIGVERIFY_SPX_CASES
]

[
    bitstream_splice(
        name = "bitstream_sigverify_spx_{}_{}".format(
            lc_state,
            t["name"],
        ),
        src = "//hw/bitstream:mask_rom",
        data = ":otp_img_sigverify_spx_{}_{}".format(
            lc_state,
            t["name"],
        ),
        meminfo = "//hw/bitstream:otp_mmi",
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
    for t in SIGVERIFY_SPX_CASES
]

[
    opentitan_test(
        name = "sigverify_spx_{}_{}".format(
            lc_state,
            t["name"],
        ),
        srcs = ["sigverify_spx_test.c"],
        ecdsa_key = ecdsa_key_for_lc_state(
            ECDSA_SPX_KEY_STRUCTS,
            lc_state_val,
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        },
        fpga = fpga_params(
            bitstream = ":bitstream_sigverify_spx_{}_{}".format(
                lc_state,
                t["name"],
            ),
            exit_success = t["exit_success"][lc_state],
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        spx_key = spx_key_for_lc_state(
            ECDSA_SPX_KEY_STRUCTS,
            lc_state_val,
        ),
        deps = [
            "//hw/ip/otp_ctrl/data:otp_ctrl_c_regs",
            "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:lifecycle",
            "//sw/device/silicon_creator/lib/drivers:otp",
            "//sw/device/silicon_creator/lib/sigverify:spx_verify",
        ],
    )
    for lc_state, lc_state_val in get_lc_items()
    for t in SIGVERIFY_SPX_CASES
]

test_suite(
    name = "rom_e2e_sigverify_spx",
    tags = ["manual"],
    tests = [
        "sigverify_spx_{}_{}".format(
            lc_state,
            t["name"],
        )
        for lc_state, _ in get_lc_items()
        for t in SIGVERIFY_SPX_CASES
    ],
)
