# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "opentitan_test",
)

def ownership_transfer_test(
        name,
        srcs = ["//sw/device/silicon_creator/rom_ext/e2e/verified_boot:boot_test"],
        exec_env = {
            "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        },
        ecdsa_key = {
            "//sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa": "app_prod",
        },
        data = [
            "//sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key",
            "//sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub",
            "//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key",
            "//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_pub",
            "//sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key",
            "//sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key",
            "//sw/device/silicon_creator/lib/ownership/keys/fake:activate_key",
            "//sw/device/silicon_creator/lib/ownership/keys/fake:owner_key",
            "//sw/device/silicon_creator/lib/ownership/keys/fake:owner_key_pub",
            "//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa_pub",
        ],
        deps = [
            "//sw/device/lib/base:status",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib:boot_log",
            "//sw/device/silicon_creator/lib/drivers:retention_sram",
        ],
        **kwargs):
    opentitan_test(
        name = name,
        srcs = srcs,
        exec_env = exec_env,
        ecdsa_key = ecdsa_key,
        data = data,
        deps = deps,
        **kwargs
    )
