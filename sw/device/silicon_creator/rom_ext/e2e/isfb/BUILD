# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST", "hex")
load(
    "//rules/opentitan:defs.bzl",
    "opentitan_binary",
)
load(
    "//sw/device/silicon_creator/rom_ext:defs.bzl",
    "ROM_EXT_VERSION",
)
load(
    "//rules:manifest.bzl",
    "integrator_specific_firmware_binding",
    "isfb_erase_allowed_policy",
    "manifest",
    "product_expr",
)

manifest(d = {
    "name": "manifest",
    "identifier": hex(CONST.ROM_EXT),
    "visibility": ["//visibility:public"],
    "version_major": ROM_EXT_VERSION.MAJOR,
    "version_minor": ROM_EXT_VERSION.MINOR,
    "security_version": ROM_EXT_VERSION.SECURITY,
    "integrator_specific_firmware_binding": integrator_specific_firmware_binding(
        name = "isfb",
        product_exprs = [
            product_expr(
                name = "constraint1",
                mask = "0xffffffff",
                value = "0xa5a5a5a5",
            ),
            product_expr(
                name = "constraint2",
                mask = "0xf0f0f0f0",
                value = "0xa0a0a0a0",
            ),
        ],
        strike_mask = "0x00000000000000000000000000000001",
    ),
    "isfb_erase_allowed_policy": isfb_erase_allowed_policy(
        name = "isfb_erase_allowed",
        erase_allowed = True,
    ),
})

opentitan_binary(
    name = "boot_test",
    testonly = True,
    srcs = ["//sw/device/silicon_creator/rom_ext/e2e/verified_boot:boot_test"],
    defines = ["WITH_OWNERSHIP_INFO=1"],
    ecdsa_key = {
        "//sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa": "app_prod",
    },
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
    },
    manifest = ":manifest",
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/ownership:datatypes",
    ],
)
