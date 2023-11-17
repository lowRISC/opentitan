# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan_test.bzl",
    "cw310_params",
    "opentitan_functest",
    "verilator_params",
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
    "opentitan_flash_binary",
    "opentitan_multislot_flash_binary",
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
    "//rules:splice.bzl",
    "bitstream_splice",
)
load(
    "//sw/device/silicon_creator/rom/e2e:defs.bzl",
    "MSG_TEMPLATE_BFV",
    "SLOTS",
)

package(default_visibility = ["//visibility:public"])

BOOT_POLICY_BAD_MANIFEST_CASES = [
    {
        "name": "bad_identifier",
        "manifest": {
            "identifier": "0",
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.BOOT_POLICY.BAD_IDENTIFIER)),
    },
    {
        "name": "too_small",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "length": hex(CONST.ROM_EXT_SIZE_MIN - 1),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.BOOT_POLICY.BAD_LENGTH)),
    },
    {
        "name": "too_large",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "length": hex(CONST.ROM_EXT_SIZE_MAX + 1),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.BOOT_POLICY.BAD_LENGTH)),
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
        "sec_ver": 1,
    },
]

[opentitan_flash_binary(
    name = "boot_policy_bad_manifest_{}_{}_bin".format(
        t["name"],
        slot,
    ),
    testonly = True,
    srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test"],
    devices = [
        "fpga_cw310",
        "sim_dv",
        "sim_verilator",
    ],
    manifest = manifest(dict(
        t["manifest"],
        name = "{}_{}".format(
            t["name"],
            slot,
        ),
    )),
    signed = True,
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_{}".format(slot),
        "//sw/device/silicon_creator/lib/sigverify:spx_verify",
    ],
) for t in BOOT_POLICY_BAD_MANIFEST_CASES for slot in SLOTS]

[opentitan_multislot_flash_binary(
    name = "boot_policy_bad_manifest_{}_{}_img".format(
        t["name"],
        slot,
    ),
    testonly = True,
    srcs = {
        "boot_policy_bad_manifest_{}_{}_bin".format(
            t["name"],
            slot,
        ): {
            "key": RSA_ONLY_KEY_STRUCTS[0],
            "offset": offset,
        },
    },
    devices = [
        "fpga_cw310",
        "sim_dv",
        "sim_verilator",
    ],
) for t in BOOT_POLICY_BAD_MANIFEST_CASES for slot, offset in SLOTS.items()]

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

# TODO: Add hyper310 targets?
[
    bitstream_splice(
        name = "bitstream_boot_policy_bad_manifest_{}_sec_ver_{}".format(
            lc_state,
            sec_ver,
        ),
        src = "//hw/bitstream:rom_with_fake_keys",
        data = ":otp_img_boot_policy_bad_manifest_{}_sec_ver_{}".format(
            lc_state,
            sec_ver,
        ),
        meminfo = "//hw/bitstream:otp_mmi",
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
    for sec_ver in [
        0,
        1,
    ]
]

[
    opentitan_functest(
        name = "boot_policy_bad_manifest_{}_{}_{}".format(
            lc_state,
            t["name"],
            slot,
        ),
        cw310 = cw310_params(
            bitstream = "bitstream_boot_policy_bad_manifest_{}_sec_ver_{}".format(
                lc_state,
                t.get("sec_ver", 0),
            ),
            exit_success = t["exit_success"],
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        key_struct = "multislot",
        ot_flash_binary = "boot_policy_bad_manifest_{}_{}_img".format(
            t["name"],
            slot,
        ),
        targets = [
            "cw310_rom_with_fake_keys",
            "verilator",
        ],
        verilator = verilator_params(
            tags = [
                # FIXME:#16056 Verilator fails to set up test.
                "broken",
            ],
        ),
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
