# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
    "opentitan_binary",
    "opentitan_test",
    "qemu_params",
)
load(
    "//sw/device/silicon_creator/rom_ext:defs.bzl",
    "ROM_EXT_VARIATIONS",
)

package(default_visibility = ["//visibility:public"])

exports_files(glob(["**"]))

VARIANTS = {
    "print_certs": {
        "rom_ext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_a",
        "test_cmd": """
            --bootstrap={firmware}
        """,
        "variation": "dice_x509",
    },
    "print_mldsa_certs": {
        "rom_ext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_mldsa_slot_a",
        "test_cmd": """
            --bootstrap={firmware}
            --timeout=60s
            --test-mldsa
        """,
        "variation": "dice_mldsa",
    },
    "print_flash_storage_mldsa_certs": {
        "manifest": "//sw/device/silicon_owner:manifest_mldsa_on_flash",
        "rom_ext": "//sw/device/silicon_creator/rom_ext:rom_ext_flash_storage_dice_mldsa",
        "test_cmd": """
            --bootstrap={firmware}
            --timeout=60s
            --test-mldsa
            --assert-mldsa-flash-storage
        """,
        "variation": "dice_mldsa",
    },
}

[
    opentitan_binary(
        name = name,
        testonly = True,
        srcs = ["print_certs.c"],
        exec_env = {
            "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
            "//hw/top_earlgrey:sim_qemu_rom_ext": None,
        },
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        manifest = info.get("manifest", None),
        slot_spec = ROM_EXT_VARIATIONS[info["variation"]].slot_spec,
        deps = [
            "//sw/device/lib/base:crc32",
            "//sw/device/lib/base:status",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/runtime:print",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/base:static_dice_cdi_0",
            "//sw/device/silicon_creator/lib/base:static_dice_mldsa_cdi",
            "//sw/device/silicon_creator/lib/base:static_dice_sections",
            "//sw/device/silicon_creator/lib/cert:dice_storage",
            "//sw/device/silicon_creator/lib/cert:ram_msg",
            "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
            "//sw/device/silicon_creator/lib/drivers:retention_sram",
            "//sw/device/silicon_creator/lib/drivers:rstmgr",
            "//sw/device/silicon_creator/manuf/base:perso_tlv_data",
        ],
    )
    for name, info in VARIANTS.items()
]

[
    opentitan_test(
        name = "{}_test".format(name),
        exec_env = {
            "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
            "//hw/top_earlgrey:sim_qemu_rom_ext": None,
        },
        fpga = fpga_params(
            binaries = {
                ":{}".format(name): "firmware",
            },
            rom_ext = info["rom_ext"],
            test_cmd = info["test_cmd"],
            test_harness = "//sw/host/tests/attestation:attestation_test",
            testopt_bootstrap = "False",
        ),
        qemu = qemu_params(
            binaries = {
                ":{}".format(name): "firmware",
            },
            rom_ext = info["rom_ext"],
            test_cmd = info["test_cmd"],
            test_harness = "//sw/host/tests/attestation:attestation_test",
        ),
        slot_spec = ROM_EXT_VARIATIONS[info["variation"]].slot_spec,
    )
    for name, info in VARIANTS.items()
]
