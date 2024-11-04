# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:const.bzl",
    "CONST",
    "get_lc_items",
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
    "otp_image",
    "otp_json",
    "otp_partition",
)
load(
    "//rules:rom_e2e.bzl",
    "maybe_skip_in_ci",
)
load(
    "//rules/opentitan:defs.bzl",
    "OTTF_SUCCESS_MSG",
    "ROM_BOOT_FAILURE_MSG",
    "cw310_params",
    "fpga_params",
    "opentitan_test",
)
load(
    "//sw/device/silicon_creator/rom/e2e:defs.bzl",
    "MSG_TEMPLATE_BFV",
    "SLOTS",
    "msg_template_bfv_all_except",
)

package(default_visibility = ["//visibility:public"])

BOOT_POLICY_BAD_MANIFEST_CASES = [
    {
        "name": "bad_identifier",
        "manifest": {
            "identifier": "0",
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.BOOT_POLICY.BAD_IDENTIFIER)),
        "exit_failure": msg_template_bfv_all_except(CONST.BFV.BOOT_POLICY.BAD_IDENTIFIER),
    },
    {
        "name": "too_small",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "length": hex(CONST.ROM_EXT_SIZE_MIN - 1),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.BOOT_POLICY.BAD_LENGTH)),
        "exit_failure": msg_template_bfv_all_except(CONST.BFV.BOOT_POLICY.BAD_LENGTH),
    },
    {
        "name": "resizable_rom_ext",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            # Note: we expect this image to boot successfully, so we must set the `address_translation` field to ensure the ROM does not error out an a bad field here.
            "address_translation": hex(CONST.HARDENED_FALSE),
            "length": hex(CONST.ROM_EXT_SIZE_MAX + 1),
        },
        "exit_success": OTTF_SUCCESS_MSG,
        "exit_failure": ROM_BOOT_FAILURE_MSG,
    },
    {
        "name": "too_large",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "length": hex(CONST.ROM_EXT_RESIZABLE_SIZE_MAX + 1),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.BOOT_POLICY.BAD_LENGTH)),
        "exit_failure": msg_template_bfv_all_except(CONST.BFV.BOOT_POLICY.BAD_LENGTH),
    },
    {
        "name": "empty_code",
        "manifest": {
            # Note: `length` is filled automatically unless overriden here.
            "identifier": hex(CONST.ROM_EXT),
            "code_start": hex(CONST.MANIFEST_SIZE + 12),
            "code_end": hex(CONST.MANIFEST_SIZE + 12),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.MANIFEST.BAD_CODE_REGION)),
        "exit_failure": msg_template_bfv_all_except(CONST.BFV.MANIFEST.BAD_CODE_REGION),
    },
    {
        "name": "code_in_manifest",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "code_start": hex(CONST.MANIFEST_SIZE - 4),
            "code_end": hex(CONST.MANIFEST_SIZE + 12),
            "entry_point": hex(CONST.MANIFEST_SIZE + 8),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.MANIFEST.BAD_CODE_REGION)),
        "exit_failure": msg_template_bfv_all_except(CONST.BFV.MANIFEST.BAD_CODE_REGION),
    },
    {
        "name": "code_outside_image",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "code_start": hex(CONST.ROM_EXT_SIZE_MAX),
            "code_end": hex(CONST.MANIFEST_SIZE + 12),
            "entry_point": hex(CONST.MANIFEST_SIZE + 8),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.MANIFEST.BAD_CODE_REGION)),
        "exit_failure": msg_template_bfv_all_except(CONST.BFV.MANIFEST.BAD_CODE_REGION),
    },
    {
        "name": "code_start_unaligned",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "code_start": hex(CONST.MANIFEST_SIZE + 6),
            "code_end": hex(CONST.MANIFEST_SIZE + 12),
            "entry_point": hex(CONST.MANIFEST_SIZE + 8),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.MANIFEST.BAD_CODE_REGION)),
        "exit_failure": msg_template_bfv_all_except(CONST.BFV.MANIFEST.BAD_CODE_REGION),
    },
    {
        "name": "code_end_unaligned",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "code_start": hex(CONST.MANIFEST_SIZE + 8),
            "code_end": hex(CONST.MANIFEST_SIZE + 10),
            "entry_point": hex(CONST.MANIFEST_SIZE + 8),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.MANIFEST.BAD_CODE_REGION)),
        "exit_failure": msg_template_bfv_all_except(CONST.BFV.MANIFEST.BAD_CODE_REGION),
    },
    {
        "name": "entry_before_code_start",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "code_start": hex(CONST.MANIFEST_SIZE + 8),
            "code_end": hex(CONST.MANIFEST_SIZE + 12),
            "entry_point": hex(CONST.MANIFEST_SIZE + 4),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.MANIFEST.BAD_ENTRY_POINT)),
        "exit_failure": msg_template_bfv_all_except(CONST.BFV.MANIFEST.BAD_ENTRY_POINT),
    },
    {
        "name": "entry_at_code_end",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "code_start": hex(CONST.MANIFEST_SIZE + 8),
            "code_end": hex(CONST.MANIFEST_SIZE + 12),
            "entry_point": hex(CONST.MANIFEST_SIZE + 12),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.MANIFEST.BAD_ENTRY_POINT)),
        "exit_failure": msg_template_bfv_all_except(CONST.BFV.MANIFEST.BAD_ENTRY_POINT),
    },
    {
        "name": "entry_unaligned",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "code_start": hex(CONST.MANIFEST_SIZE + 8),
            "code_end": hex(CONST.MANIFEST_SIZE + 12),
            "entry_point": hex(CONST.MANIFEST_SIZE + 10),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.MANIFEST.BAD_ENTRY_POINT)),
        "exit_failure": msg_template_bfv_all_except(CONST.BFV.MANIFEST.BAD_ENTRY_POINT),
    },
    {
        "name": "rollback",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "code_start": hex(CONST.MANIFEST_SIZE + 8),
            "code_end": hex(CONST.MANIFEST_SIZE + 12),
            "entry_point": hex(CONST.MANIFEST_SIZE + 8),
            "security_version": "0",
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.BOOT_POLICY.ROLLBACK)),
        "exit_failure": msg_template_bfv_all_except(CONST.BFV.BOOT_POLICY.ROLLBACK),
        "sec_ver": 1,
    },
]

[
    otp_json(
        name = "otp_json_sec_ver_{}".format(sec_ver),
        partitions = [
            otp_partition(
                name = "CREATOR_SW_CFG",
                items = {
                    "CREATOR_SW_CFG_MIN_SEC_VER_ROM_EXT": "{}".format(sec_ver),
                },
            ),
        ],
    )
    for sec_ver in [
        0,
        1,
    ]
]

[
    otp_image(
        name = "otp_img_boot_policy_bad_manifest_{}_sec_ver_{}".format(
            lc_state,
            sec_ver,
        ),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS + [":otp_json_sec_ver_{}".format(sec_ver)],
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
    for sec_ver in [
        0,
        1,
    ]
]

[
    manifest(dict(
        t["manifest"],
        name = "{}_{}".format(
            t["name"],
            slot,
        ),
    ))
    for t in BOOT_POLICY_BAD_MANIFEST_CASES
    for slot in SLOTS
]

[
    opentitan_test(
        name = "boot_policy_bad_manifest_{}_{}_{}".format(
            lc_state,
            t["name"],
            slot,
        ),
        srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test"],
        # Use the prod key because it is valid in every LC state.
        ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        },
        fpga = fpga_params(
            assemble = "{firmware}@{offset}",
            exit_failure = t["exit_failure"],
            exit_success = t["exit_success"],
            offset = SLOTS[slot],
            otp = ":otp_img_boot_policy_bad_manifest_{}_sec_ver_{}".format(
                lc_state,
                t.get("sec_ver", 0),
            ),
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_{}".format(slot),
        manifest = ":{}_{}".format(
            t["name"],
            slot,
        ),
        deps = [
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for lc_state, lc_state_val in get_lc_items()
    for t in BOOT_POLICY_BAD_MANIFEST_CASES
    for slot in SLOTS
]

test_suite(
    name = "rom_e2e_boot_policy_bad_manifest",
    tags = ["manual"],
    tests = [
        "boot_policy_bad_manifest_{}_{}_{}".format(
            lc_state,
            t["name"],
            slot,
        )
        for lc_state, _ in get_lc_items()
        for t in BOOT_POLICY_BAD_MANIFEST_CASES
        for slot in SLOTS
    ],
)
