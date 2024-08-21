# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:const.bzl",
    "CONST",
    "hex",
    "hex_digits",
)
load(
    "//rules:manifest.bzl",
    "manifest",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_hex",
    "otp_image",
    "otp_json",
    "otp_partition",
)
load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
    "opentitan_binary",
    "opentitan_test",
)
load(
    "//sw/device/silicon_creator/rom/e2e:defs.bzl",
    "SLOTS",
)

package(default_visibility = ["//visibility:public"])

FLASH_ECC_ERROR_CAUSES = [
    {
        "cause": "manifest_security_version",
        "id": 0,
    },
    {
        "cause": "manifest_identifier",
        "id": 1,
    },
    {
        "cause": "manifest_length",
        "id": 2,
    },
    {
        "cause": "manifest_manifest_version",
        "id": 3,
    },
    {
        "cause": "manifest_signed_region_end",
        "id": 4,
    },
    {
        "cause": "manifest_code_start",
        "id": 5,
    },
    {
        "cause": "manifest_code_end",
        "id": 6,
    },
    {
        "cause": "manifest_entry_point",
        "id": 7,
    },
    {
        "cause": "manifest_ecdsa_public_key",
        "id": 8,
    },
    {
        "cause": "manifest_usage_constraints_selector_bits",
        "id": 9,
    },
    {
        "cause": "manifest_ecdsa_signature",
        "id": 10,
    },
    {
        "cause": "manifest_extension_spx_public_key",
        "id": 11,
    },
    {
        "cause": "manifest_extension_spx_signature",
        "id": 12,
    },
    # We only test corrupting the first flash word since this is likely not in
    # the range of test code that needs to execute successfully to drive the
    # test, but still exercising the scenario of a flash corruption happening
    # in the code region.
    {
        "cause": "code_first_word",
        "id": 13,
    },
]

BOOT_POLICY_FLASH_ECC_ERROR_TESTS = [
    {
        "name": "a_corrupt_b_valid_{}",
        "a": ":flash_ecc_self_corruption_slot_a_{}",
        "b": ":uncorrupted_test_slot_b",
        "exit_success": "Booted slot=0x20080000; Cause={}",
    },
    {
        "name": "a_valid_b_corrupt_{}",
        "a": ":uncorrupted_test_slot_a",
        "b": ":flash_ecc_self_corruption_slot_b_{}",
        "exit_success": "Booted slot=0x20000000; Cause={}",
    },
]

otp_json(
    name = "otp_json_flash_data_cfg_default_scr_and_ecc_enabled",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                # Enable flash data page scrambling and ECC.
                "CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG": "0000090606",
                # Enable SPX+ signature verification.
                "CREATOR_SW_CFG_SIGVERIFY_SPX_EN": otp_hex(CONST.HARDENED_TRUE),
            },
        ),
    ],
)

otp_json(
    name = "otp_json_flash_exc_handler_disabled",
    partitions = [
        otp_partition(
            name = "OWNER_SW_CFG",
            items = {
                "OWNER_SW_CFG_ROM_FLASH_ECC_EXC_HANDLER_EN": otp_hex(CONST.HARDENED_FALSE),
            },
        ),
    ],
)

otp_image(
    name = "otp_img_boot_policy_flash_ecc_error",
    src = "//hw/ip/otp_ctrl/data:otp_json_prod",
    overlays = STD_OTP_OVERLAYS + [":otp_json_flash_data_cfg_default_scr_and_ecc_enabled"],
    visibility = ["//visibility:private"],
)

otp_image(
    name = "otp_img_flash_exc_handler_disabled",
    src = "//hw/ip/otp_ctrl/data:otp_json_prod",
    overlays = STD_OTP_OVERLAYS + [
        ":otp_json_flash_data_cfg_default_scr_and_ecc_enabled",
        ":otp_json_flash_exc_handler_disabled",
    ],
    visibility = ["//visibility:private"],
)

SEC_VERS = [
    0,
    1,
]

[
    manifest({
        "name": "manifest_sec_ver_{}".format(sec_ver),
        "address_translation": hex(CONST.HARDENED_FALSE),
        "identifier": hex(CONST.ROM_EXT),
        "security_version": hex(sec_ver),
    })
    for sec_ver in SEC_VERS
]

[
    opentitan_binary(
        name = "uncorrupted_test_slot_{}".format(slot),
        testonly = True,
        srcs = ["uncorrupted_test.c"],
        # Use the prod key because it is valid in every LC state.
        ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
        exec_env = [
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys",
        ],
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_{}".format(slot),
        # This image always get the lower security version as we want the image that self-corrupts the ECC
        # of the manifest identifier to always boot first, befause attempting to boot this (known-good) image.
        manifest = ":manifest_sec_ver_0",
        spx_key = {"//sw/device/silicon_creator/rom/keys/fake/spx:prod_key_0_spx": "prod_key_0"},
        deps = [
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib:manifest_def",
            "//sw/device/silicon_creator/lib/drivers:retention_sram",
        ],
    )
    for slot in SLOTS
]

[
    opentitan_binary(
        name = "flash_ecc_self_corruption_slot_{}_{}".format(
            slot,
            c["cause"],
        ),
        testonly = True,
        srcs = ["flash_ecc_error_test.c"],
        # Use the prod key because it is valid in every LC state.
        ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
        exec_env = [
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys",
        ],
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_{}".format(slot),
        local_defines = [
            "CAUSE_ID={}".format(c["id"]),
        ],
        # This image always get the higher security version as we want it to always boot first.
        manifest = ":manifest_sec_ver_1",
        spx_key = {"//sw/device/silicon_creator/rom/keys/fake/spx:prod_key_0_spx": "prod_key_0"},
        deps = [
            "//hw/ip/otp_ctrl/data:otp_ctrl_c_regs",
            "//hw/top_earlgrey/ip_autogen/flash_ctrl:flash_ctrl_c_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/base:macros",
            "//sw/device/lib/base:status",
            "//sw/device/lib/dif:flash_ctrl",
            "//sw/device/lib/dif:otp_ctrl",
            "//sw/device/lib/dif:rstmgr",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:flash_ctrl_testutils",
            "//sw/device/lib/testing:otp_ctrl_testutils",
            "//sw/device/lib/testing:rstmgr_testutils",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib:boot_data",
            "//sw/device/silicon_creator/lib:boot_log",
            "//sw/device/silicon_creator/lib:manifest",
            "//sw/device/silicon_creator/lib:manifest_def",
            "//sw/device/silicon_creator/lib/base:chip",
            "//sw/device/silicon_creator/lib/drivers:retention_sram",
            "//sw/device/silicon_creator/rom:boot_policy_ptrs",
        ],
    )
    for slot in SLOTS
    for c in FLASH_ECC_ERROR_CAUSES
]

[
    opentitan_test(
        name = t["name"].format(c["cause"]),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        },
        fpga = fpga_params(
            assemble = "{fw_a}@{slot_a} {fw_b}@{slot_b}",
            binaries = {
                t["a"].format(c["cause"]): "fw_a",
                t["b"].format(c["cause"]): "fw_b",
            },
            exit_success = t["exit_success"].format(c["cause"]),
            otp = ":otp_img_boot_policy_flash_ecc_error",
            slot_a = SLOTS["a"],
            slot_b = SLOTS["b"],
        ),
    )
    for t in BOOT_POLICY_FLASH_ECC_ERROR_TESTS
    for c in FLASH_ECC_ERROR_CAUSES
]

opentitan_test(
    name = "flash_exc_handler_disabled_test",
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    fpga = fpga_params(
        assemble = "{fw_a}@{slot_a} {fw_b}@{slot_b}",
        binaries = {
            ":flash_ecc_self_corruption_slot_a_manifest_identifier": "fw_a",
            ":uncorrupted_test_slot_b": "fw_b",
        },
        # Since the flash ecc exception handler is disabled in this test,
        # we expect to see a load access fault when the ROM accesses the
        # corrupted flash word.
        exit_success = "BFV:{}".format(hex_digits(CONST.BFV.INTERRUPT.LOAD_ACCESS)),
        otp = ":otp_img_flash_exc_handler_disabled",
        slot_a = SLOTS["a"],
        slot_b = SLOTS["b"],
    ),
)

test_suite(
    name = "boot_policy_flash_ecc_error",
    tags = ["manual"],
    tests = [
        t["name"].format(c["cause"])
        for t in BOOT_POLICY_FLASH_ECC_ERROR_TESTS
        for c in FLASH_ECC_ERROR_CAUSES
    ],
)
