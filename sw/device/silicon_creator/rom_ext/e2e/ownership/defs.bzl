# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@lowrisc_opentitan//rules/opentitan:defs.bzl",
    "opentitan_test",
)

def ownership_transfer_test(
        name,
        srcs = ["@lowrisc_opentitan//sw/device/silicon_creator/rom_ext/e2e/verified_boot:boot_test"],
        exec_env = {
            "@lowrisc_opentitan//hw/top_earlgrey:fpga_cw310_rom_ext": None,
        },
        ecdsa_key = {
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa": "app_prod",
        },
        manifest = None,
        data = [
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_pub",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key_spx",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_spx",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_spx_pub",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key_spx",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/fake:activate_key",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/fake:owner_key",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/fake:owner_key_pub",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key_spx",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/fake:activate_key_spx",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/fake:owner_key_spx",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/fake:owner_key_spx_pub",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa_pub",
        ],
        defines = ["WITH_OWNERSHIP_INFO=1"],
        deps = [
            "@lowrisc_opentitan//sw/device/lib/base:status",
            "@lowrisc_opentitan//sw/device/lib/testing/test_framework:ottf_main",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib:boot_log",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/drivers:flash_ctrl",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/drivers:retention_sram",
            "@lowrisc_opentitan//sw/device/silicon_creator/lib/ownership:datatypes",
        ],
        **kwargs):
    opentitan_test(
        name = name,
        srcs = srcs,
        exec_env = exec_env,
        ecdsa_key = ecdsa_key,
        manifest = manifest,
        data = data,
        defines = defines,
        deps = deps,
        **kwargs
    )
