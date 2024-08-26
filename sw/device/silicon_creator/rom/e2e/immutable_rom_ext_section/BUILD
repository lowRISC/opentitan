# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@bazel_skylib//lib:dicts.bzl",
    "dicts",
)
load(
    "//rules:const.bzl",
    "CONST",
    "hex",
    "hex_digits",
)
load(
    "//sw/device/silicon_creator/rom_ext:defs.bzl",
    "ROM_EXT_VERSION",
)
load("//rules:manifest.bzl", "manifest")
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_hex",
    "otp_image",
    "otp_json_immutable_rom_ext",
    "otp_partition",
)
load(
    "//rules/opentitan:defs.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
    "DEFAULT_TEST_SUCCESS_MSG",
    "fpga_params",
    "opentitan_binary",
    "opentitan_test",
)
load(
    "//sw/device/silicon_creator/rom/e2e:defs.bzl",
    "MSG_TEMPLATE_BFV",
)

package(default_visibility = ["//visibility:public"])

ROM_EXT_LINKER_SCRIPTS = [
    "a",
    "virtual",
]

IMMUTABLE_PARTITION_TEST_CASES = [
    {
        "name": "exec_enabled_hash_valid",
        "otp_fields": {
            "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN": otp_hex(CONST.HARDENED_TRUE),
        },
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    {
        "name": "exec_enabled_hash_invalid",
        "otp_fields": {
            "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN": otp_hex(CONST.HARDENED_TRUE),
            "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_SHA256_HASH": otp_hex(0x1234),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.INTERRUPT.ILLEGAL_INSTRUCTION)),
        "exit_failure": DEFAULT_TEST_SUCCESS_MSG,
    },
    {
        "name": "exec_disabled_hash_valid",
        "otp_fields": {
            "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN": otp_hex(CONST.HARDENED_FALSE),
        },
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    {
        "name": "exec_disabled_hash_invalid",
        "otp_fields": {
            "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN": otp_hex(CONST.HARDENED_FALSE),
            "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_SHA256_HASH": otp_hex(0x1234),
        },
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    {
        "name": "exec_empty_hash_valid",
        "otp_fields": {},
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    {
        "name": "exec_empty_hash_invalid",
        "otp_fields": {
            "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_SHA256_HASH": otp_hex(0x1234),
        },
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    {
        "name": "exec_enabled_start_offset_invalid",
        "otp_fields": {
            "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN": otp_hex(CONST.HARDENED_TRUE),
            "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_START_OFFSET": otp_hex(0x4),
        },
        # The hash check should fail, since the offset is included in the hash,
        # triggering a hardened check fail (which executes an unimp; triggering
        # an exception and shutdown).
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.INTERRUPT.ILLEGAL_INSTRUCTION)),
        "exit_failure": DEFAULT_TEST_SUCCESS_MSG,
    },
    {
        "name": "exec_disabled_start_offset_invalid",
        "otp_fields": {
            "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN": otp_hex(CONST.HARDENED_FALSE),
            "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_START_OFFSET": otp_hex(0x4),
        },
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    {
        "name": "exec_enabled_length_invalid",
        "otp_fields": {
            "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN": otp_hex(CONST.HARDENED_TRUE),
            "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_LENGTH": otp_hex(0x4),
        },
        # The hash check should fail, since the length is included in the hash,
        # triggering a hardened check fail (which executes an unimp; triggering
        # an exception and shutdown).
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.INTERRUPT.ILLEGAL_INSTRUCTION)),
        "exit_failure": DEFAULT_TEST_SUCCESS_MSG,
    },
    {
        "name": "exec_disabled_length_invalid",
        "otp_fields": {
            "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN": otp_hex(CONST.HARDENED_FALSE),
            "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_LENGTH": otp_hex(0x4),
        },
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
]

[
    otp_json_immutable_rom_ext(
        name = "otp_json_immutable_rom_ext_{}_{}".format(
            t["name"],
            ld_script,
        ),
        testonly = True,
        partitions = [
            otp_partition(
                name = "CREATOR_SW_CFG",
                items = t["otp_fields"],
            ),
        ],
        rom_ext = ":immutable_rom_ext_section_test_{}".format(ld_script),
        visibility = ["//visibility:private"],
    )
    for ld_script in ROM_EXT_LINKER_SCRIPTS
    for t in IMMUTABLE_PARTITION_TEST_CASES
]

[
    otp_image(
        name = "otp_img_immutable_rom_ext_{}_{}".format(
            t["name"],
            ld_script,
        ),
        testonly = True,
        src = "//hw/ip/otp_ctrl/data:otp_json_prod",
        overlays = STD_OTP_OVERLAYS + [
            ":otp_json_immutable_rom_ext_{}_{}".format(
                t["name"],
                ld_script,
            ),
        ],
        visibility = ["//visibility:private"],
    )
    for ld_script in ROM_EXT_LINKER_SCRIPTS
    for t in IMMUTABLE_PARTITION_TEST_CASES
]

_MANIFEST_CONFIG = {
    "identifier": hex(CONST.ROM_EXT),
    "version_major": ROM_EXT_VERSION.MAJOR,
    "version_minor": ROM_EXT_VERSION.MINOR,
    "security_version": ROM_EXT_VERSION.SECURITY,
}

manifest(d = dicts.add(
    _MANIFEST_CONFIG,
    {
        "name": "manifest_addr_trans_on",
        "address_translation": hex(CONST.HARDENED_TRUE),
    },
))

manifest(d = dicts.add(
    _MANIFEST_CONFIG,
    {
        "name": "manifest_addr_trans_off",
        "address_translation": hex(CONST.HARDENED_FALSE),
    },
))

[
    opentitan_binary(
        name = "immutable_rom_ext_section_test_{}".format(ld_script),
        testonly = True,
        srcs = ["immutable_rom_ext_section_test.c"],
        exec_env = [
            "//hw/top_earlgrey:fpga_cw310_sival",
        ],
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_{}".format(ld_script),
        manifest = ":manifest_addr_trans_on" if ld_script == "virtual" else ":manifest_addr_trans_off",
        deps = [
            "//hw/ip/otp_ctrl/data:otp_ctrl_c_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:hardened",
            "//sw/device/lib/base:status",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:otp",
            "//sw/device/silicon_creator/lib/drivers:retention_sram",
            "//sw/device/silicon_creator/lib/drivers:uart",
        ],
    )
    for ld_script in ROM_EXT_LINKER_SCRIPTS
]

[
    opentitan_test(
        name = "immutable_section_{}_{}".format(
            t["name"],
            ld_script,
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
        fpga = fpga_params(
            binaries = {
                ":immutable_rom_ext_section_test_{}".format(ld_script): "firmware",
            },
            exit_failure = t["exit_failure"],
            exit_success = t["exit_success"],
            otp = ":otp_img_immutable_rom_ext_{}_{}".format(
                t["name"],
                ld_script,
            ),
        ),
    )
    for ld_script in ROM_EXT_LINKER_SCRIPTS
    for t in IMMUTABLE_PARTITION_TEST_CASES
]

test_suite(
    name = "immutable_rom_ext_section",
    tags = ["manual"],
    tests = [
        "immutable_section_{}_{}".format(
            t["name"],
            ld_script,
        )
        for ld_script in ROM_EXT_LINKER_SCRIPTS
        for t in IMMUTABLE_PARTITION_TEST_CASES
    ],
)
