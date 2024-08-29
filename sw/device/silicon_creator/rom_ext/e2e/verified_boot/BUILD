# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load(
    "//rules/opentitan:defs.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
    "DEFAULT_TEST_SUCCESS_MSG",
    "EARLGREY_TEST_ENVS",
    "cw310_params",
    "fpga_params",
    "opentitan_test",
)
load("//rules:const.bzl", "CONST", "hex")
load("//rules:manifest.bzl", "manifest")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "boot_test",
    srcs = ["boot_test.c"],
)

_POSITIONS = {
    "owner_slot_a": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a",
        "romext_offset": "0",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "0x10000",
        "success": "bl0_slot = AA__\r\n",
    },
    "owner_slot_b": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a",
        "romext_offset": "0",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_b",
        "owner_offset": "0x90000",
        "success": "bl0_slot = __BB\r\n",
    },
    "owner_virtual_a": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a",
        "romext_offset": "0",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
        "owner_offset": "0x10000",
        "success": "bl0_slot = AA__\r\n",
    },
    "owner_virtual_b": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a",
        "romext_offset": "0",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
        "owner_offset": "0x90000",
        "success": "bl0_slot = __BB\r\n",
    },
    "romext_slot_a": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a",
        "romext_offset": "0",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "0x10000",
        "success": "rom_ext_slot = AA__\r\n",
    },
    "romext_slot_b": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_slot_b",
        "romext_offset": "0x80000",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "0x10000",
        "success": "rom_ext_slot = __BB\r\n",
    },
    "romext_virtual_a": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_slot_virtual",
        "romext_offset": "0",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "0x10000",
        "success": "rom_ext_slot = AA__\r\n",
    },
    "romext_virtual_b": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_slot_virtual",
        "romext_offset": "0x80000",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "0x10000",
        "success": "rom_ext_slot = __BB\r\n",
    },
}

[
    opentitan_test(
        name = "position_{}".format(name),
        srcs = [":boot_test"],
        exec_env = {
            "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        },
        fpga = fpga_params(
            assemble = "{romext}@{romext_offset} {firmware}@{owner_offset}",
            binaries = {
                position["romext"]: "romext",
            },
            exit_success = position["success"],
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
    "prod": {
        "key": {"//sw/device/silicon_creator/rom_ext/keys/fake:rom_ext_prod_private_key_0": "prod_key_0"},
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    "test": {
        "key": {"//sw/device/silicon_creator/rom_ext/keys/fake:rom_ext_test_private_key_0": "test_key_0"},
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    "dev": {
        "key": {"//sw/device/silicon_creator/rom_ext/keys/fake:rom_ext_dev_private_key_0": "dev_key_0"},
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    "unauthorized": {
        "key": {"//sw/device/silicon_creator/rom/keys/unauthorized/rsa:unauthorized_private_key_0": "unauthorized_key_0"},
        "exit_success": DEFAULT_TEST_FAILURE_MSG,
        "exit_failure": DEFAULT_TEST_SUCCESS_MSG,
    },
}

[
    opentitan_test(
        name = "key_{}".format(name),
        srcs = [":boot_test"],
        exec_env = {
            "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        },
        fpga = fpga_params(
            exit_failure = keyinfo["exit_failure"],
            exit_success = keyinfo["exit_success"],
        ),
        rsa_key = keyinfo["key"],
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
