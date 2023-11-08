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
    "hex",
    "hex_digits",
)
load(
    "//rules:manifest.bzl",
    "manifest",
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
load(
    "//sw/device/silicon_creator/rom/e2e:defs.bzl",
    "MSG_PASS",
    "MSG_TEMPLATE_BFV",
)

package(default_visibility = ["//visibility:public"])

BOOT_DATA_RECOVERY_CASES = [
    {
        "lc_state": "test_unlocked0",
        "min_sec_ver": 0,
        "default_boot_data": "nodefault",
        "expected_bfv": None,
    },
    {
        "lc_state": "dev",
        "min_sec_ver": 1,
        "default_boot_data": "nodefault",
        "expected_bfv": None,
    },
    {
        "lc_state": "prod",
        "min_sec_ver": 1,
        "default_boot_data": "default",
        "expected_bfv": None,
    },
    {
        "lc_state": "prod",
        "min_sec_ver": 0,
        "default_boot_data": "nodefault",
        "expected_bfv": CONST.BFV.BOOT_DATA.NOT_FOUND,
    },
    {
        "lc_state": "prod_end",
        "min_sec_ver": 0,
        "default_boot_data": "default",
        "expected_bfv": None,
    },
    {
        "lc_state": "prod_end",
        "min_sec_ver": 1,
        "default_boot_data": "nodefault",
        "expected_bfv": CONST.BFV.BOOT_DATA.NOT_FOUND,
    },
    {
        "lc_state": "rma",
        "min_sec_ver": 0,
        "default_boot_data": "nodefault",
        "expected_bfv": None,
    },
]

[
    otp_json(
        name = "boot_data_recovery_creator_sw_cfg_{}_{}".format(
            case["lc_state"],
            case["default_boot_data"],
        ),
        partitions = [
            otp_partition(
                name = "CREATOR_SW_CFG",
                items = {
                    # Set the min_sec version.
                    "CREATOR_SW_CFG_MIN_SEC_VER_ROM_EXT": otp_hex(case["min_sec_ver"]),
                    # Set allowing use of default boot data in PROD LC state.
                    "CREATOR_SW_CFG_DEFAULT_BOOT_DATA_IN_PROD_EN": otp_hex(
                        CONST.HARDENED_TRUE if case["default_boot_data"] == "default" else CONST.HARDENED_FALSE,
                    ),
                },
            ),
        ],
    )
    for case in BOOT_DATA_RECOVERY_CASES
]

[
    otp_image(
        name = "otp_img_boot_data_recovery_{}_{}".format(
            case["lc_state"],
            case["default_boot_data"],
        ),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(case["lc_state"]),
        overlays = STD_OTP_OVERLAYS + [":boot_data_recovery_creator_sw_cfg_{}_{}".format(
            case["lc_state"],
            case["default_boot_data"],
        )],
    )
    for case in BOOT_DATA_RECOVERY_CASES
]

[
    bitstream_splice(
        name = "bitstream_boot_data_recovery_{}_{}".format(
            case["lc_state"],
            case["default_boot_data"],
        ),
        src = "//hw/bitstream/hyperdebug:rom_with_fake_keys",
        data = ":otp_img_boot_data_recovery_{}_{}".format(
            case["lc_state"],
            case["default_boot_data"],
        ),
        meminfo = "//hw/bitstream/hyperdebug:otp_mmi",
        tags = maybe_skip_in_ci(getattr(
            CONST.LCV,
            case["lc_state"].upper(),
        )),
        update_usr_access = True,
    )
    for case in BOOT_DATA_RECOVERY_CASES
]

BOOT_DATA_RECOVERY_MANIFEST = manifest(
    d = dict(
        name = "boot_data_recovery_manifest",
        address_translation = hex(CONST.HARDENED_FALSE),
        identifier = hex(CONST.ROM_EXT),
        security_version = hex(2),
    ),
)

[
    opentitan_test(
        name = "boot_data_recovery_{}_{}".format(
            case["lc_state"],
            case["default_boot_data"],
        ),
        srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test"],
        cw310 = cw310_params(
            bitstream = ":bitstream_boot_data_recovery_{}_{}".format(
                case["lc_state"],
                case["default_boot_data"],
            ),
            exit_success = MSG_TEMPLATE_BFV.format(hex_digits(case["expected_bfv"])) if case["expected_bfv"] != None else MSG_PASS,
            tags = maybe_skip_in_ci(getattr(
                CONST.LCV,
                case["lc_state"].upper(),
            )),
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        },
        manifest = BOOT_DATA_RECOVERY_MANIFEST,
        # PROD keys can sign binaries able to run across all life cycle states.
        rsa_key = rsa_key_for_lc_state(
            RSA_ONLY_KEY_STRUCTS,
            CONST.LCV.PROD,
        ),
        deps = [
            "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:otp",
            "//sw/device/silicon_creator/lib/sigverify:spx_verify",
        ],
    )
    for case in BOOT_DATA_RECOVERY_CASES
]

test_suite(
    name = "rom_e2e_boot_data_recovery",
    tags = ["manual"],
    tests = [
        "boot_data_recovery_{}_{}".format(
            case["lc_state"],
            case["default_boot_data"],
        )
        for case in BOOT_DATA_RECOVERY_CASES
    ],
)
