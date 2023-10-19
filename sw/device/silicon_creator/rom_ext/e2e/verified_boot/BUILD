# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load(
    "//rules/opentitan:defs.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
    "DEFAULT_TEST_SUCCESS_MSG",
    "EARLGREY_TEST_ENVS",
    "cw310_params",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

_POSITIONS = {
    "slot_a": {
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "manifest": "//sw/device/silicon_owner:manifest_standard",
        "offset": "0x10000",
    },
    "slot_b": {
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_b",
        "manifest": "//sw/device/silicon_owner:manifest_standard",
        "offset": "0x90000",
    },
    "virtual_a": {
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
        "manifest": "//sw/device/silicon_owner:manifest_virtual",
        "offset": "0x10000",
    },
    "virtual_b": {
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
        "manifest": "//sw/device/silicon_owner:manifest_virtual",
        "offset": "0x90000",
    },
}

[
    opentitan_test(
        name = "position_{}".format(name),
        srcs = ["boot_test.c"],
        cw310 = cw310_params(
            assemble = "{rom_ext}@0 {firmware}@{offset}",
            bitstream = "//sw/device/silicon_creator/rom_ext/e2e:bitstream_secret2_locked",
            offset = position["offset"],
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
        },
        linker_script = position["linker_script"],
        manifest = position["manifest"],
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
        srcs = ["boot_test.c"],
        cw310 = cw310_params(
            bitstream = "//sw/device/silicon_creator/rom_ext/e2e:bitstream_secret2_locked",
            exit_failure = keyinfo["exit_failure"],
            exit_success = keyinfo["exit_success"],
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
        },
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
