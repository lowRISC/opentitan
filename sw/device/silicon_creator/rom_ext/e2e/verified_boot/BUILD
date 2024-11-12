# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "CLEAR_KEY_SET",
    "DEFAULT_TEST_FAILURE_MSG",
    "DEFAULT_TEST_SUCCESS_MSG",
    "EARLGREY_TEST_ENVS",
    "cw310_params",
    "fpga_params",
    "opentitan_test",
)
load("//rules:const.bzl", "CONST", "hex")
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
    "//sw/device/silicon_creator/rom_ext/imm_section:defs.bzl",
    "IMMUTABLE_HASH_UNENFORCED_MSG",
    "IMM_SECTION_VARIATIONS",
)

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "boot_test",
    srcs = ["boot_test.c"],
)

[
    otp_json_immutable_rom_ext(
        name = "otp_json_with_{}_imm_romext_enabled".format(name),
        testonly = True,
        partitions = [
            otp_partition(
                name = "CREATOR_SW_CFG",
                items = {
                    "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN": otp_hex(CONST.HARDENED_TRUE),
                },
            ),
        ],
        rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_with_{}_imm_slot_virtual".format(name),
        visibility = ["//visibility:private"],
    )
    for name in IMM_SECTION_VARIATIONS
]

[
    otp_image(
        name = "otp_img_with_{}_imm_romext_enabled".format(name),
        testonly = True,
        src = "//hw/top_earlgrey/data/otp:otp_json_prod",
        overlays = STD_OTP_OVERLAYS + [
            "//sw/device/silicon_creator/rom_ext/e2e:otp_json_secret2_locked",
            ":otp_json_with_{}_imm_romext_enabled".format(name),
        ],
        visibility = ["//visibility:private"],
    )
    for name in IMM_SECTION_VARIATIONS
]

_POSITIONS = {
    "owner_slot_a": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a",
        "romext_offset": "0",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "0x10000",
        "success": "bl0_slot = AA__\r\n",
        "otp_img": None,
    },
    "owner_slot_b": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a",
        "romext_offset": "0",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_b",
        "owner_offset": "0x90000",
        "success": "bl0_slot = __BB\r\n",
        "otp_img": None,
    },
    "owner_virtual_a": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a",
        "romext_offset": "0",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
        "owner_offset": "0x10000",
        "success": "bl0_slot = AA__\r\n",
        "otp_img": None,
    },
    "owner_virtual_b": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a",
        "romext_offset": "0",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
        "owner_offset": "0x90000",
        "success": "bl0_slot = __BB\r\n",
        "otp_img": None,
    },
    "romext_slot_a": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a",
        "romext_offset": "0",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "0x10000",
        "success": "rom_ext_slot = AA__\r\n",
        "otp_img": None,
    },
    "romext_slot_b": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_slot_b",
        "romext_offset": "0x80000",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "0x10000",
        "success": "rom_ext_slot = __BB\r\n",
        "otp_img": None,
    },
    "romext_virtual_a": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_slot_virtual",
        "romext_offset": "0",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "0x10000",
        "success": "rom_ext_slot = AA__\r\n",
        "otp_img": None,
    },
    "romext_virtual_b": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_slot_virtual",
        "romext_offset": "0x80000",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "0x10000",
        "success": "rom_ext_slot = __BB\r\n",
        "otp_img": None,
    },
} | {
    "romext_virtual_a_with_{}_imm_romext_enabled".format(name): {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_with_{}_imm_slot_virtual".format(name),
        "romext_offset": "0",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "0x10000",
        "success": "rom_ext_slot = AA__\r\n",
        "failure": IMMUTABLE_HASH_UNENFORCED_MSG,
        "otp_img": ":otp_img_with_{}_imm_romext_enabled".format(name),
    }
    for name in IMM_SECTION_VARIATIONS
}

[
    opentitan_test(
        name = "position_{}".format(name),
        srcs = [":boot_test"],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
            "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        },
        fpga = fpga_params(
            assemble = "{romext}@{romext_offset} {firmware}@{owner_offset}",
            binaries = {
                position["romext"]: "romext",
            },
            exit_failure = position.get("failure", DEFAULT_TEST_FAILURE_MSG),
            exit_success = position["success"],
            otp = position["otp_img"],
            owner_offset = position["owner_offset"],
            romext_offset = position["romext_offset"],
        ),
        linker_script = position["linker_script"],
        deps = [
            "//sw/device/lib/base:status",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib:boot_log",
            "//sw/device/silicon_creator/lib/drivers:retention_sram",
        ],
    )
    for name, position in _POSITIONS.items()
]

test_suite(
    name = "positions",
    tests = ["position_{}".format(name) for name in _POSITIONS],
)

manifest(d = {
    "name": "bad_manifest",
    "address_translation": hex(CONST.HARDENED_FALSE),
    "identifier": hex(CONST.OWNER),
    "manifest_version_major": "0",
    "manifest_version_minor": "0",
    "visibility": ["//visibility:public"],
})

opentitan_test(
    name = "bad_manifest_test",
    srcs = [":boot_test"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
    },
    fpga = fpga_params(
        exit_failure = "PASS|FAIL|FAULT|BFV:.{8}",
        # Because our bad manifest has an invalid manifest version, we should
        # expect kErrorManifestBadVersionMajor from the ROM_EXT.
        exit_success = "BFV:054d410d",
    ),
    manifest = ":bad_manifest",
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

_KEYS = {
    "dev": {
        "ecdsa": {"//sw/device/silicon_creator/lib/ownership/keys/fake:app_dev_ecdsa": "dev_key_0"},
        "spx": {},
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    "dev_hybrid": {
        "ecdsa": {"//sw/device/silicon_creator/lib/ownership/keys/fake:app_dev_ecdsa": "dev_key_0"},
        "spx": {"//sw/device/silicon_creator/lib/ownership/keys/fake:app_dev_spx": "dev_key_0"},
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    "prod": {
        "ecdsa": {"//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa": "prod_key_0"},
        "spx": {},
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    "prod_hybrid": {
        "ecdsa": {"//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa": "prod_key_0"},
        "spx": {"//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_spx": "prod_key_0"},
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    "test": {
        "ecdsa": {"//sw/device/silicon_creator/lib/ownership/keys/fake:app_test_ecdsa": "test_key_0"},
        "spx": {},
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    "unauthorized": {
        "ecdsa": {"//sw/device/silicon_creator/lib/ownership/keys/fake:app_unauthorized_ecdsa": "unauthorized_key_0"},
        "spx": {},
        "exit_success": DEFAULT_TEST_FAILURE_MSG,
        "exit_failure": DEFAULT_TEST_SUCCESS_MSG,
    },
}

[
    opentitan_test(
        name = "key_{}".format(name),
        srcs = [":boot_test"],
        ecdsa_key = keyinfo["ecdsa"],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
            "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        },
        fpga = fpga_params(
            exit_failure = keyinfo["exit_failure"],
            exit_success = keyinfo["exit_success"],
        ),
        spx_key = keyinfo["spx"],
        deps = [
            "//sw/device/lib/base:status",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib:boot_log",
            "//sw/device/silicon_creator/lib/drivers:retention_sram",
        ],
    )
    for name, keyinfo in _KEYS.items()
]

test_suite(
    name = "keys",
    tests = ["key_{}".format(name) for name in _KEYS],
)
