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
)
load(
    "//rules:opentitan.bzl",
    "RSA_SPX_KEY_STRUCTS",
    "get_key_structs_for_lc_state",
    "opentitan_flash_binary",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_bytestring",
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
load(
    "@bazel_skylib//lib:dicts.bzl",
    "dicts",
)
load(
    "@bazel_skylib//lib:shell.bzl",
    "shell",
)

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
                lc_state: "spx_en=0x00000000, spx_en_otp=0x00000000, spx_key_en=0x4ba5a5a5a5a5a5a5"
                for lc_state in SPX_OTP_LC_STATES
            },
            {
                lc_state: "spx_en=0x8d6c8c17, spx_en_otp=0x00000000, spx_key_en=0x4ba5a5a5a5a5a5a5"
                for lc_state in SPX_DISABLED_LC_STATES
            },
        ),
    },
    {
        "name": "enabled_true",
        "spx_en": CONST.HARDENED_TRUE,
        "exit_success": dicts.add(
            {
                lc_state: "spx_en=0x00000739, spx_en_otp=0x00000739, spx_key_en=0x4ba5a5a5a5a5a5a5"
                for lc_state in SPX_OTP_LC_STATES
            },
            {
                lc_state: "spx_en=0x8d6c8c17, spx_en_otp=0x00000739, spx_key_en=0x4ba5a5a5a5a5a5a5"
                for lc_state in SPX_DISABLED_LC_STATES
            },
        ),
    },
    {
        "name": "disabled",
        "spx_en": CONST.SPX_DISABLED,
        "exit_success": {
            lc_state: "spx_en=0x8d6c8c17, spx_en_otp=0x8d6c8c17, spx_key_en=0x4ba5a5a5a5a5a5a5"
            for lc_state in SPX_OTP_LC_STATES + SPX_DISABLED_LC_STATES
        },
    },
]

opentitan_flash_binary(
    name = "empty_test_sigverify_spx",
    testonly = True,
    srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test"],
    devices = [
        "fpga_cw310",
        "sim_dv",
        "sim_verilator",
    ],
    local_defines = [
        shell.quote("EMPTY_TEST_MSG=\"spx_en=0x%08x, spx_en_otp=0x%08x, spx_key_en=0x%08x%08x\", " +
                    "sigverify_spx_verify_enabled(lifecycle_state_get()), " +
                    "otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_SPX_EN_OFFSET), " +
                    "otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_SPX_KEY_EN_OFFSET + sizeof(uint32_t)), " +
                    "otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_SPX_KEY_EN_OFFSET)"),
    ],
    signed = True,
    signing_key_structs = RSA_SPX_KEY_STRUCTS,
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
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
                    "CREATOR_SW_CFG_SIGVERIFY_SPX_KEY_EN": otp_bytestring([
                        CONST.HARDENED_BYTE_TRUE,  # key0
                        CONST.HARDENED_BYTE_TRUE,  # key1
                        CONST.HARDENED_BYTE_TRUE,  # key2
                        CONST.HARDENED_BYTE_TRUE,  # key3
                        CONST.HARDENED_BYTE_TRUE,  # key4
                        CONST.HARDENED_BYTE_TRUE,  # key5
                        CONST.HARDENED_BYTE_TRUE,  # key6
                        CONST.HARDENED_BYTE_FALSE,  # key7
                    ]),
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
        overlays = STD_OTP_OVERLAYS + [":otp_json_sigverify_spx_{}".format(t["name"])],
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
    for t in SIGVERIFY_SPX_CASES
]

# TODO: Add hyper310 targets?
[
    bitstream_splice(
        name = "bitstream_sigverify_spx_{}_{}".format(
            lc_state,
            t["name"],
        ),
        src = "//hw/bitstream:rom_with_fake_keys",
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
    opentitan_functest(
        name = "sigverify_spx_{}_{}".format(
            lc_state,
            t["name"],
        ),
        cw310 = cw310_params(
            bitstream = ":bitstream_sigverify_spx_{}_{}".format(
                lc_state,
                t["name"],
            ),
            exit_success = t["exit_success"][lc_state],
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        key_struct = get_key_structs_for_lc_state(lc_state_val)[0],
        ot_flash_binary = ":empty_test_sigverify_spx",
        targets = ["cw310_rom_with_fake_keys"],
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
