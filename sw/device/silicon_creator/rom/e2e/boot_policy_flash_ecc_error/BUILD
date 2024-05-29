# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_image",
    "otp_json",
    "otp_partition",
)
load(
    "//rules:manifest.bzl",
    "manifest",
)
load(
    "//rules:const.bzl",
    "CONST",
    "hex",
)
load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "opentitan_binary",
    "opentitan_test",
)
load(
    "//sw/device/silicon_creator/rom/e2e:defs.bzl",
    "SLOTS",
)

package(default_visibility = ["//visibility:public"])

BOOT_POLICY_FLASH_ECC_ERROR_CASES = [
    {
        "name": "a_corrupt_b_valid",
        "a": ":flash_ecc_self_corruption_slot_a",
        "b": ":empty_test_slot_b",
    },
    {
        "name": "a_valid_b_corrupt",
        "a": ":empty_test_slot_a",
        "b": ":flash_ecc_self_corruption_slot_b",
    },
    # TODO(#21353): add test case for both images corrupted.
]

otp_json(
    name = "otp_json_flash_data_cfg_default_unprovisioned",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                # Enable flash data page scrambling and ECC.
                "CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG": "0000090606",
            },
        ),
    ],
)

otp_image(
    name = "otp_img_boot_policy_flash_ecc_error",
    src = "//hw/ip/otp_ctrl/data:otp_json_prod",
    overlays = STD_OTP_OVERLAYS + [":otp_json_flash_data_cfg_default_unprovisioned"],
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
        name = "empty_test_slot_{}".format(slot),
        testonly = True,
        srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test"],
        # Use the prod key because it is valid in every LC state.
        ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
        exec_env = [
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys",
        ],
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_{}".format(slot),
        local_defines = [
            "EMPTY_TEST_MSG=\"slot=%p, security_version=%01d, lc_state=0x%08x\", manifest_def_get(), manifest_def_get()->security_version, lifecycle_raw_state_get()",
        ],
        # This image always get the lower security version as we want the image that self-corrupts the ECC
        # of the manifest identifier to always boot first, befause attempting to boot this (known-good) image.
        manifest = ":manifest_sec_ver_0",
        deps = [
            "//hw/ip/otp_ctrl/data:otp_ctrl_c_regs",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:lifecycle",
            "//sw/device/silicon_creator/lib/drivers:otp",
            "//sw/device/silicon_creator/lib/sigverify:spx_verify",
        ],
    )
    for slot in SLOTS
]

[
    opentitan_binary(
        name = "flash_ecc_self_corruption_slot_{}".format(slot),
        testonly = True,
        srcs = ["flash_ecc_error_test.c"],
        # Use the prod key because it is valid in every LC state.
        ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
        exec_env = [
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys",
        ],
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_{}".format(slot),
        local_defines = ["CORRUPT_SLOT_{}_ID=\"1\"".format(slot.upper())],
        # This image always get the higher security version as we want it to always boot first.
        manifest = ":manifest_sec_ver_1",
        deps = [
            "//hw/ip/otp_ctrl/data:otp_ctrl_c_regs",
            "//hw/top_earlgrey/ip_autogen/flash_ctrl/data:flash_ctrl_c_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/base:status",
            "//sw/device/lib/dif:flash_ctrl",
            "//sw/device/lib/dif:otp_ctrl",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:flash_ctrl_testutils",
            "//sw/device/lib/testing:otp_ctrl_testutils",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/base:chip",
        ],
    )
    for slot in SLOTS
]

[
    opentitan_test(
        name = "boot_policy_flash_ecc_error_{}".format(c["name"]),
        cw310 = cw310_params(
            assemble = "{fw_a}@{slot_a} {fw_b}@{slot_b}",
            binaries = {
                c["a"]: "fw_a",
                c["b"]: "fw_b",
            },
            otp = ":otp_img_boot_policy_flash_ecc_error",
            slot_a = SLOTS["a"],
            slot_b = SLOTS["b"],
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        },
    )
    for c in BOOT_POLICY_FLASH_ECC_ERROR_CASES
]

test_suite(
    name = "boot_policy_flash_ecc_error",
    tags = ["manual"],
    tests = [
        "boot_policy_flash_ecc_error_{}".format(c["name"])
        for c in BOOT_POLICY_FLASH_ECC_ERROR_CASES
    ],
)
