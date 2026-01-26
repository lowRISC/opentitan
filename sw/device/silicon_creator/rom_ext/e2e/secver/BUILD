# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST", "hex", "hex_digits")
load("//rules:cross_platform.bzl", "dual_cc_library", "dual_inputs")
load("//rules:linker.bzl", "ld_library")
load("//rules:manifest.bzl", "manifest")
load("//rules/opentitan:defs.bzl", "fpga_params", "opentitan_binary", "opentitan_test")
load(
    "//sw/device/silicon_creator/rom_ext:defs.bzl",
    "ROM_EXT_VARIATIONS",
    "ROM_EXT_VERSION",
    "SLOTS",
    "TEST_OWNER_CONFIGS",
)

package(default_visibility = ["//visibility:public"])

manifest(d = {
    "name": "manifest0",
    "identifier": hex(CONST.ROM_EXT),
    "visibility": ["//visibility:public"],
    "version_major": "0",
    "version_minor": "0",
    "security_version": "0",
    "secver_write": "false",
})

manifest(d = {
    "name": "manifest1",
    "identifier": hex(CONST.ROM_EXT),
    "visibility": ["//visibility:public"],
    "version_major": "0",
    "version_minor": "1",
    "security_version": "1",
    "secver_write": "true",
})

manifest(d = {
    "name": "manifest2",
    "identifier": hex(CONST.ROM_EXT),
    "visibility": ["//visibility:public"],
    "version_major": "0",
    "version_minor": "2",
    "security_version": "2",
    "secver_write": "false",
})

manifest(d = {
    "name": "manifest3",
    "identifier": hex(CONST.ROM_EXT),
    "visibility": ["//visibility:public"],
    "version_major": "0",
    "version_minor": "3",
    "security_version": "3",
    "secver_write": "true",
})

_TEST_ROM_EXTS = {
    "0": {
        "manifest": ":manifest0",
    },
    "1": {
        "manifest": ":manifest1",
    },
    "2": {
        "manifest": ":manifest2",
    },
    "3": {
        "manifest": ":manifest3",
    },
}

[
    opentitan_binary(
        name = "rom_ext_{}".format(name),
        testonly = True,
        ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:ecdsa_keyset": "prod_key_0"},
        exec_env = [
            "//hw/top_earlgrey:fpga_cw310",
            "//hw/top_earlgrey:fpga_cw340",
        ],
        extra_bazel_features = [
            "minsize",
            "use_lld",
        ],
        linker_script = "//sw/device/silicon_creator/rom_ext:ld_slot_virtual",
        manifest = param["manifest"],
        spx_key = {"//sw/device/silicon_creator/rom/keys/fake/spx:spx_keyset": "prod_key_0"},
        deps = [
            "//sw/device/lib/crt",
            "//sw/device/silicon_creator/lib:manifest_def",
            "//sw/device/silicon_creator/lib/ownership:test_owner",
            "//sw/device/silicon_creator/lib/ownership/keys/fake",
            "//sw/device/silicon_creator/lib/rescue:rescue_xmodem",
            "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509",
            "//sw/device/silicon_creator/rom_ext/imm_section:main_section_dice_x509_slot_virtual",
        ],
    )
    for name, param in _TEST_ROM_EXTS.items()
]

opentitan_test(
    name = "secver_write_test",
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
    },
    fpga = fpga_params(
        timeout = "long",
        assemble = "{rom_ext}@{rom_ext_slot_a} {boot_test}@{owner_slot_a}",
        binaries = {
            ":boot_test": "boot_test",
            ":rom_ext_1": "rom_ext1",
            ":rom_ext_2": "rom_ext2",
            ":rom_ext_3": "rom_ext3",
        },
        exit_success = "BFV:{}".format(hex_digits(CONST.BFV.BOOT_POLICY.ROLLBACK)),
        rom_ext = ":rom_ext_0",
        test_cmd = """
            # First, assemble the additional images we'll need for this test.
            --exec="image assemble -s 524288 --mirror=false -o fw1.bin {rom_ext1}@{rom_ext_slot_a} {boot_test}@{owner_slot_a}"
            --exec="image assemble -s 524288 --mirror=false -o fw2.bin {rom_ext2}@{rom_ext_slot_a} {boot_test}@{owner_slot_a}"
            --exec="image assemble -s 524288 --mirror=false -o fw3.bin {rom_ext3}@{rom_ext_slot_a} {boot_test}@{owner_slot_a}"

            # Check the initial version 0 has been bootstrapped into SlotA
            --exec="console --non-interactive --exit-success='rom_ext_min_sec_ver = 0'"

            # Rescue and update to SlotB.  We expect to update the secver.
            --exec="rescue firmware --raw --slot=SlotB fw1.bin"
            --exec="console --non-interactive --exit-success='rom_ext_min_sec_ver = 1'"

            # Rescue and update to SlotA.  We expect NOT to update the secver.
            --exec="rescue firmware --raw --slot=SlotA fw2.bin"
            --exec="console --non-interactive --exit-success='rom_ext_min_sec_ver = 1'"

            # Rescue and update to SlotB.  We expect to update the secver.
            --exec="rescue firmware --raw --slot=SlotB fw3.bin"
            --exec="console --non-interactive --exit-success='rom_ext_min_sec_ver = 3'"

            # Finally, bootstrap back to version 0, which we expect NOT to work.
            --exec="bootstrap --clear-uart=true {firmware}"
            --exec="console --non-interactive --exit-success='{exit_success}' --timeout=10s"
            no-op
        """,
        testopt_clear_after_test = "True",
        testopt_clear_before_test = "True",
    ),
)

opentitan_binary(
    name = "boot_test",
    testonly = True,
    srcs = ["//sw/device/silicon_creator/rom_ext/e2e/verified_boot:boot_test"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
    },
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)
