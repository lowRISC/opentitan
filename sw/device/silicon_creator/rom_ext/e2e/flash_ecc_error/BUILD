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
load(
    "//sw/device/silicon_creator/rom/e2e/boot_policy_flash_ecc_error:defs.bzl",
    "BOOT_POLICY_FLASH_ECC_ERROR_TESTS",
    "FLASH_ECC_ERROR_CAUSES",
    "SEC_VERS",
)

package(default_visibility = ["//visibility:public"])

otp_json(
    name = "otp_json_flash_data_cfg_default_scr_and_ecc_enabled",
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
    name = "otp_img_flash_ecc_error",
    src = "//hw/top_earlgrey/data/otp:otp_json_prod",
    overlays = STD_OTP_OVERLAYS + [
        ":otp_json_flash_data_cfg_default_scr_and_ecc_enabled",
    ],
    visibility = ["//visibility:private"],
)

otp_image(
    name = "otp_img_flash_exc_handler_disabled",
    src = "//hw/top_earlgrey/data/otp:otp_json_prod",
    overlays = STD_OTP_OVERLAYS + [
        ":otp_json_flash_data_cfg_default_scr_and_ecc_enabled",
        ":otp_json_flash_exc_handler_disabled",
    ],
    visibility = ["//visibility:private"],
)

opentitan_binary(
    name = "secret_page_setup",
    testonly = True,
    srcs = ["secret_page_setup.c"],
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys",
    ],
    deps = [
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

[
    opentitan_binary(
        name = "uncorrupted_test_slot_{}".format(slot),
        testonly = True,
        srcs = ["//sw/device/silicon_creator/rom/e2e/boot_policy_flash_ecc_error:uncorrupted_test_src"],
        exec_env = [
            "//hw/top_earlgrey:fpga_cw310_rom_ext",
        ],
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_{}".format(slot),
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
        srcs = ["//sw/device/silicon_creator/rom/e2e/boot_policy_flash_ecc_error:flash_ecc_error_test_src"],
        exec_env = [
            "//hw/top_earlgrey:fpga_cw310_rom_ext",
        ],
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_{}".format(slot),
        local_defines = [
            "CAUSE_ID={}".format(c["id"]),
        ],
        spx_key = {"//sw/device/silicon_creator/lib/ownership/keys/fake:app_spx_prod": "app_prod_0"},
        deps = [
            "//hw/top:flash_ctrl_c_regs",
            "//hw/top:otp_ctrl_c_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/arch:boot_stage",
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
            "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
        },
        fpga = fpga_params(
            assemble = "{rom_ext}@0 {fw_a}@{slot_a} {rom_ext}@0x80000 {fw_b}@{slot_b}",
            binaries = {
                t["a"].format(c["cause"]): "fw_a",
                t["b"].format(c["cause"]): "fw_b",
                ":secret_page_setup": "setup",
            },
            exit_success = t["exit_success"].format(c["cause"]),
            otp = ":otp_img_flash_ecc_error",
            primary = t["primary"],
            rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_virtual",
            slot_a = "0x10000",
            slot_b = "0x90000",
            test_cmd = """
                --exec="transport init"
                --exec="fpga load-bitstream {bitstream}"
                # First run the setup program to make sure the keymgr secrets are configured.
                # This is required to allow the ROM_EXT to run.
                --exec="bootstrap --clear-uart=true {setup}"
                --exec="console --non-interactive --exit-success='PASS!' --exit-failure='FAIL'"
                # Next bootstrap the ROM_EXT alone so we can use boot services to set the
                # primary slot.  This makes sure we boot the correct slot first.
                --exec="bootstrap --clear-uart=true {rom_ext}"
                --exec="rescue boot-svc set-next-bl0-slot --primary={primary} --get-response=true"
                # Finally, boot the full firmware payload, which will corrupt a portion of
                # the flash and ensure that the ROM_EXT exception handler can handle it.
                --exec="bootstrap --clear-uart=true {firmware}"
                --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
                no-op
            """,
        ),
    )
    for t in BOOT_POLICY_FLASH_ECC_ERROR_TESTS
    for c in FLASH_ECC_ERROR_CAUSES
]

opentitan_test(
    name = "flash_exc_handler_disabled_test",
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
    },
    fpga = fpga_params(
        assemble = "{rom_ext}@0 {fw_a}@{slot_a} {rom_ext}@0x80000 {fw_b}@{slot_b}",
        binaries = {
            ":flash_ecc_self_corruption_slot_a_manifest_identifier": "fw_a",
            ":uncorrupted_test_slot_b": "fw_b",
            ":secret_page_setup": "setup",
        },
        exit_failure = "PASS!",
        # Since the flash ecc exception handler is disabled in this test,
        # we expect to see a load access fault when the ROM accesses the
        # corrupted flash word.
        exit_success = "BFV:{}".format(hex_digits(CONST.BFV.ROM_EXT_INTR.LOAD_ACCESS)),
        otp = ":otp_img_flash_exc_handler_disabled",
        primary = "SlotA",
        rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_virtual",
        slot_a = "0x10000",
        slot_b = "0x90000",
        test_cmd = """
            --exec="transport init"
            --exec="fpga load-bitstream {bitstream}"
            # First run the setup program to make sure the keymgr secrets are configured.
            # This is required to allow the ROM_EXT to run.
            --exec="bootstrap --clear-uart=true {setup}"
            --exec="console --non-interactive --exit-success='PASS!' --exit-failure='FAIL'"
            # Next bootstrap the ROM_EXT alone so we can use boot services to set the
            # primary slot.  This makes sure we boot the correct slot first.
            --exec="bootstrap --clear-uart=true {rom_ext}"
            --exec="rescue boot-svc set-next-bl0-slot --primary={primary} --get-response=true"
            # Finally, boot the full firmware payload, which will corrupt a portion of
            # the flash and ensure that the ROM_EXT exception handler can handle it.
            --exec="bootstrap --clear-uart=true {firmware}"
            --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
            no-op
        """,
    ),
)

test_suite(
    name = "flash_ecc_error",
    tags = ["manual"],
    tests = [
        t["name"].format(c["cause"])
        for t in BOOT_POLICY_FLASH_ECC_ERROR_TESTS
        for c in FLASH_ECC_ERROR_CAUSES
    ],
)
