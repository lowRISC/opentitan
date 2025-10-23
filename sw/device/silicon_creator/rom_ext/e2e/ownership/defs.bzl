# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
    "opentitan_test",
    "qemu_params",
)
load("@bazel_skylib//lib:structs.bzl", "structs")

def ownership_transfer_test(
        name,
        srcs = ["//sw/device/silicon_creator/rom_ext/e2e/verified_boot:boot_test"],
        exec_env = {
            "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
            "//hw/top_earlgrey:sim_qemu_rom_ext": None,
        },
        ecdsa_key = {
            "//sw/device/silicon_creator/lib/ownership/keys/dummy:ecdsa_keyset": "app_prod_0",
        },
        manifest = None,
        data = [
            "//sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key",
            "//sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub",
            "//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key",
            "//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_pub",
            "//sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key",
            "//sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key_spx",
            "//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_spx",
            "//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_spx_pub",
            "//sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key_spx",
            "//sw/device/silicon_creator/lib/ownership/keys/dummy:all_zero_sig",
            "//sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key",
            "//sw/device/silicon_creator/lib/ownership/keys/fake:activate_key",
            "//sw/device/silicon_creator/lib/ownership/keys/fake:owner_key",
            "//sw/device/silicon_creator/lib/ownership/keys/fake:no_owner_recovery_key",
            "//sw/device/silicon_creator/lib/ownership/keys/fake:owner_key_pub",
            "//sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key_spx",
            "//sw/device/silicon_creator/lib/ownership/keys/fake:activate_key_spx",
            "//sw/device/silicon_creator/lib/ownership/keys/fake:owner_key_spx",
            "//sw/device/silicon_creator/lib/ownership/keys/fake:owner_key_spx_pub",
            "//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa_pub",
        ],
        defines = ["WITH_OWNERSHIP_INFO=1"],
        deps = [
            "//sw/device/lib/base:status",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib:boot_log",
            "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
            "//sw/device/silicon_creator/lib/drivers:retention_sram",
            "//sw/device/silicon_creator/lib/ownership:datatypes",
        ],
        fpga = None,
        qemu = None,
        shared_params = None,
        **kwargs):
    # FPGA should always clear the bitstream & bootstrap first, so
    # enable these on every FPGA test unless overridden
    fpga = {
        "testopt_clear_after_test": "True",
        "testopt_clear_before_test": "True",
        "testopt_bootstrap": "True",
    } | (shared_params or {}) | (fpga or {})
    fpga = fpga_params(**fpga)

    # Construct `qemu_params` from shared and QEMU-specific parameters
    if shared_params:
        override_params = dict(shared_params)
        if qemu:
            override_params.update(qemu)

        # QEMU takes longer to emulate entering rescue due to slow
        # emulation of the ROM, as a result of the `sec_mmio` code hot
        # loops falling in a misaligned EPMP region that effectively
        # disables QEMU's TCG TLB optimisations. As such, we always
        # increase the delay to enter rescue to 20s on QEMU targets.
        # This is likely much larger than needed, but should give some
        # lenience for tests being run in parallel or on slower hosts.
        override_params["test_cmd"] = """
            --rescue-enter-delay=20s
            --bootstrap={firmware}
        """ + override_params["test_cmd"]

        # XModem-CRC transfer as part of the rescue flow uses somewhat
        # tight timing based on the UART baud rate, which depends on
        # the performance & load of the host. Change the icount shift
        # used to make timing more lenient on QEMU, albeit at the cost
        # of longer test executions.
        if not qemu or "icount" not in qemu:
            override_params["icount"] = "5"
        qemu = qemu_params(**override_params)
    else:
        qemu = qemu_params(**qemu)

    opentitan_test(
        name = name,
        srcs = srcs,
        exec_env = exec_env,
        ecdsa_key = ecdsa_key,
        manifest = manifest,
        data = data,
        defines = defines,
        deps = deps,
        fpga = fpga,
        qemu = qemu,
        **kwargs
    )
