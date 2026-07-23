# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST", "hex")
load(
    "//rules:manifest.bzl",
    "integrator_specific_firmware_binding",
    "manifest",
    "product_expr",
)
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
    "opentitan_test",
    "qemu_params",
)
load(
    "//sw/device/silicon_creator/rom_ext:defs.bzl",
    "ROM_EXT_VARIATIONS",
)
load(
    "//sw/device/silicon_creator/rom_ext/imm_section:defs.bzl",
    "IMMUTABLE_HASH_UNENFORCED_MSG",
    "IMM_SECTION_MAJOR_VERSION",
    "IMM_SECTION_MINOR_VERSION",
)

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "boot_test",
    srcs = ["boot_test.c"],
)

otp_json_immutable_rom_ext(
    name = "otp_json_with_imm_romext_enabled",
    testonly = True,
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN": otp_hex(CONST.HARDENED_TRUE),
            },
        ),
    ],
    rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_virtual",
    visibility = ["//visibility:private"],
)

otp_image(
    name = "otp_img_with_imm_romext_enabled",
    testonly = True,
    src = "//hw/ip/otp_ctrl/data:otp_json_prod",
    overlays = STD_OTP_OVERLAYS + [
        "//sw/device/silicon_creator/rom_ext/e2e:otp_json_secret2_locked",
        ":otp_json_with_imm_romext_enabled",
    ],
    visibility = ["//visibility:private"],
)

_POSITIONS = {
    "owner_slot_a": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_a",
        "romext_offset": "{rom_ext_slot_a}",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "{owner_slot_a}",
        "success": "bl0_slot = AA__\r\n",
        "otp_img": None,
    },
    "owner_slot_a_absent_base_address": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_a",
        "romext_offset": "{rom_ext_slot_a}",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "{owner_slot_a}",
        "success": "bl0_slot = AA__\r\n",
        "otp_img": None,
        "manifest": ":manifest_base_address_default",
    },
    "owner_slot_b": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_a",
        "romext_offset": "{rom_ext_slot_a}",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_b",
        "owner_offset": "{owner_slot_b}",
        "success": r"bl0_slot = __BB[\s\S]*boot_log bl0_failure_reason = 0142500d",
        "otp_img": None,
    },
    "owner_slot_b_shifted": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_mldsa_slot_a",
        "romext_offset": "{rom_ext_slot_a}",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_b",
        "owner_offset": "{owner_slot_b}",
        "success": "bl0_slot = __BB\r\n",
        "otp_img": None,
        "slot_spec": ROM_EXT_VARIATIONS["dice_mldsa"].slot_spec,
    },
    "owner_virtual_a": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_a",
        "romext_offset": "{rom_ext_slot_a}",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
        "owner_offset": "{owner_slot_a}",
        "success": "bl0_slot = AA__\r\n",
        "otp_img": None,
    },
    "owner_virtual_b": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_a",
        "romext_offset": "{rom_ext_slot_a}",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
        "owner_offset": "{owner_slot_b}",
        "success": "bl0_slot = __BB\r\n",
        "otp_img": None,
    },
    "owner_virtual_b_shifted": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_mldsa_slot_a",
        "romext_offset": "{rom_ext_slot_a}",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
        "owner_offset": "{owner_slot_b}",
        "success": "bl0_slot = __BB\r\n",
        "otp_img": None,
        "slot_spec": ROM_EXT_VARIATIONS["dice_mldsa"].slot_spec,
    },
    "romext_slot_a": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_a",
        "romext_offset": "{rom_ext_slot_a}",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "{owner_slot_a}",
        "success": "rom_ext_slot = AA__\r\n",
        "otp_img": None,
    },
    "romext_slot_b": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_b",
        "romext_offset": "{rom_ext_slot_b}",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "{owner_slot_a}",
        "success": "rom_ext_slot = __BB\r\n",
        "otp_img": None,
    },
    "romext_virtual_a": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_virtual",
        "romext_offset": "{rom_ext_slot_a}",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "{owner_slot_a}",
        "success": "rom_ext_slot = AA__\r\n",
        "otp_img": None,
    },
    "romext_virtual_b": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_virtual",
        "romext_offset": "{rom_ext_slot_b}",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "{owner_slot_a}",
        "success": "rom_ext_slot = __BB\r\n",
        "otp_img": None,
    },
    "romext_virtual_a_with_imm_romext_enabled": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_virtual",
        "romext_offset": "{rom_ext_slot_a}",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "{owner_slot_a}",
        "success": "rom_ext_slot = AA__\r\n",
        "failure": IMMUTABLE_HASH_UNENFORCED_MSG,
        "otp_img": ":otp_img_with_imm_romext_enabled",
    },
    "imm_section_virtual_a": {
        "romext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_virtual",
        "romext_offset": "{rom_ext_slot_a}",
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "owner_offset": "{owner_slot_a}",
        "success": "IMM_SECTION:{}.{}".format(IMM_SECTION_MAJOR_VERSION, IMM_SECTION_MINOR_VERSION),
        "otp_img": None,
    },
}

[
    opentitan_test(
        name = "position_{}".format(name),
        srcs = [":boot_test"],
        exec_env = {
            "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
            "//hw/top_earlgrey:sim_qemu_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw340_a2_rom_ext": None,
            "//hw/top_earlgrey:sim_qemu_a2_rom_ext": None,
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
        manifest = position.get("manifest", None),
        qemu = qemu_params(
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
        slot_spec = position.get("slot_spec", {}),
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
    "name": "manifest_base_address_mismatch",
    "address_translation": hex(CONST.HARDENED_TRUE),
    "manifest_base_address": "0x10000000",
    "identifier": hex(CONST.OWNER),
    "visibility": ["//visibility:public"],
})

manifest(d = {
    "name": "manifest_base_address_default",
    "manifest_base_address": "0xa5a5a5a5",
    "identifier": hex(CONST.OWNER),
    "visibility": ["//visibility:public"],
})

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
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        "//hw/top_earlgrey:sim_qemu_rom_ext": None,
    },
    fpga = fpga_params(
        exit_failure = "PASS|FAIL|FAULT|BFV:.{8}",
        # Because our bad manifest has an invalid manifest version, we should
        # expect kErrorManifestBadVersionMajor from the ROM_EXT.
        exit_success = "BFV:054d410d",
    ),
    manifest = ":bad_manifest",
    qemu = qemu_params(
        exit_failure = "PASS|FAIL|FAULT|BFV:.{8}",
        exit_success = "BFV:054d410d",
    ),
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

opentitan_test(
    name = "bad_base_address_manifest_test",
    srcs = [":boot_test"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        "//hw/top_earlgrey:sim_qemu_rom_ext": None,
    },
    fpga = fpga_params(
        exit_failure = "PASS|FAIL|FAULT|BFV:.{8}",
        # Because our bad manifest has an invalid base address, we should
        # expect kErrorManifestBadBaseAddress from the ROM_EXT.
        exit_success = "BFV:064d410d",
    ),
    manifest = ":manifest_base_address_mismatch",
    qemu = qemu_params(
        exit_failure = "PASS|FAIL|FAULT|BFV:.{8}",
        # BFV:064d410d corresponds to kErrorManifestBadBaseAddress
        exit_success = "BFV:064d410d",
    ),
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

opentitan_test(
    name = "bad_base_address_absent_large_rom_ext_test",
    srcs = [":boot_test"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        "//hw/top_earlgrey:sim_qemu_rom_ext": None,
    },
    fpga = fpga_params(
        assemble = "{romext}@{romext_offset} {firmware}@{owner_slot_a}",
        binaries = {
            "//sw/device/silicon_creator/rom_ext:rom_ext_dice_mldsa_slot_a": "romext",
        },
        exit_failure = "PASS|FAIL|FAULT|BFV:.{8}",
        # BFV:064d410d corresponds to kErrorManifestBadBaseAddress
        exit_success = "BFV:064d410d",
        romext_offset = "0x0",
    ),
    manifest = ":manifest_base_address_default",
    qemu = qemu_params(
        assemble = "{romext}@{romext_offset} {firmware}@{owner_slot_a}",
        binaries = {
            "//sw/device/silicon_creator/rom_ext:rom_ext_dice_mldsa_slot_a": "romext",
        },
        exit_failure = "PASS|FAIL|FAULT|BFV:.{8}",
        # BFV:064d410d corresponds to kErrorManifestBadBaseAddress
        exit_success = "BFV:064d410d",
        romext_offset = "0x0",
    ),
    slot_spec = ROM_EXT_VARIATIONS["dice_mldsa"].slot_spec,
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

manifest(d = {
    "name": "bad_spx_manifest",
    "address_translation": hex(CONST.HARDENED_FALSE),
    "identifier": hex(CONST.OWNER),
    "visibility": ["//visibility:public"],
    "extensions": [
        "spx_key",
        "",
        "secver_write",
        "isfb",
        "isfb_erase",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "",
        "spx_signature",
    ],
})

opentitan_test(
    name = "bad_spx_manifest_test",
    srcs = [":boot_test"],
    ecdsa_key = {"//sw/device/silicon_creator/lib/ownership/keys/fake:ecdsa_keyset": "app_prod_0"},
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        "//hw/top_earlgrey:sim_qemu_rom_ext": None,
    },
    fpga = fpga_params(
        exit_failure = "PASS|FAIL|FAULT|BFV:.{8}",
        # Because our bad manifest placed spx_signature in a wrong slot, we
        # should expect kErrorManifestBadExtension from the ROM_EXT.
        exit_success = "BFV:044d410d",
    ),
    manifest = ":bad_spx_manifest",
    qemu = qemu_params(
        exit_failure = "PASS|FAIL|FAULT|BFV:.{8}",
        exit_success = "BFV:044d410d",
    ),
    spx_key = {"//sw/device/silicon_creator/lib/ownership/keys/fake:spx_keyset": "app_prod_0"},
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

_KEYS = {
    "dev": {
        "ecdsa": {"//sw/device/silicon_creator/lib/ownership/keys/fake:ecdsa_keyset": "app_dev_0"},
        "spx": {},
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    "dev_hybrid_spx_prehashed": {
        "ecdsa": {"//sw/device/silicon_creator/lib/ownership/keys/fake:ecdsa_keyset": "app_dev_0"},
        "spx": {"//sw/device/silicon_creator/lib/ownership/keys/fake:spx_keyset": "app_dev_0"},
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    "prod": {
        "ecdsa": {"//sw/device/silicon_creator/lib/ownership/keys/fake:ecdsa_keyset": "app_prod_0"},
        "spx": {},
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    "prod_hybrid_spx_pure": {
        "ecdsa": {"//sw/device/silicon_creator/lib/ownership/keys/fake:ecdsa_keyset": "app_prod_0"},
        "spx": {"//sw/device/silicon_creator/lib/ownership/keys/fake:spx_keyset": "app_prod_0"},
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    "test": {
        "ecdsa": {"//sw/device/silicon_creator/lib/ownership/keys/fake:ecdsa_keyset": "app_test_0"},
        "spx": {},
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    "unauthorized": {
        "ecdsa": {"//sw/device/silicon_creator/lib/ownership/keys/fake:ecdsa_keyset": "app_unauthorized_0"},
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
            "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
            "//hw/top_earlgrey:sim_qemu_rom_ext": None,
        },
        fpga = fpga_params(
            exit_failure = keyinfo["exit_failure"],
            exit_success = keyinfo["exit_success"],
        ),
        qemu = qemu_params(
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

manifest(d = {
    "name": "isfb_manifest",
    "address_translation": hex(CONST.HARDENED_FALSE),
    "identifier": hex(CONST.OWNER),
    "visibility": ["//visibility:public"],
    "integrator_specific_firmware_binding": integrator_specific_firmware_binding(
        name = "isfb",
        product_exprs = [
            product_expr(
                name = "none",
                mask = "0xFFFFFFFF",
                value = "0xFFFFFFFF",
            ),
        ],
        strike_mask = "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
    ),
})

opentitan_test(
    name = "isfb_boot_test",
    srcs = [":boot_test"],
    ecdsa_key = {"//sw/device/silicon_creator/lib/ownership/keys/fake:ecdsa_keyset": "app_prod_0"},
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        "//hw/top_earlgrey:sim_qemu_rom_ext": None,
    },
    fpga = fpga_params(),
    manifest = ":isfb_manifest",
    spx_key = {"//sw/device/silicon_creator/lib/ownership/keys/fake:spx_keyset": "app_prod_0"},
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)
