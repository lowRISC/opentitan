# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
    "opentitan_binary",
    "opentitan_test",
)
load(
    "//sw/device/silicon_creator/rom_ext/e2e/ownership:defs.bzl",
    "ownership_transfer_test",
)
load("//rules:const.bzl", "CONST", "hex")
load("//rules:manifest.bzl", "manifest")

package(default_visibility = ["//visibility:public"])

# TODO(#24462): The tests in this file are marked `changes_otp = True`,
# but they don't change OTP.  They modify the ownership INFO pages,
# so we need to clear the bitstream after the test, which is what the
# `changes_otp` parameter actually does.

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
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/ownership:datatypes",
    ],
)

opentitan_binary(
    name = "flash_regions",
    testonly = True,
    srcs = ["flash_regions.c"],
    ecdsa_key = {
        "//sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa": "app_prod",
    },
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
    },
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

# This manifest is node-locked to the DEVICE_ID provided by the ROM_EXT E2E OTP
# configuration //sw/device/silicon_creator/rom_ext/e2e:otp_img_secret2_locked_rma,
# and required by the exec_env `fpga_hyper310_rom_ext`.
manifest({
    "name": "nodelocked_manifest",
    "identifier": hex(CONST.OWNER),
    "device_id": [
        hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
        hex(0x66666666),
        hex(0x55555555),
    ],
    "visibility": ["//visibility:public"],
})

# rom_ext_e2e_testplan.hjson%rom_ext_e2e_transfer_any_test
ownership_transfer_test(
    name = "transfer_any_test",
    fpga = fpga_params(
        changes_otp = True,
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --unlock-mode=Any
            --unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key)
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub)
        """,
        test_harness = "//sw/host/tests/ownership:transfer_test",
    ),
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

ownership_transfer_test(
    name = "bad_appkey_constraint_test",
    fpga = fpga_params(
        changes_otp = True,
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --unlock-mode=Any
            --unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key)
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub)
            --config-kind=with-app-constraint
            --expected-error=SigverifyBadEcdsaSignature
        """,
        test_harness = "//sw/host/tests/ownership:transfer_test",
    ),
)

ownership_transfer_test(
    name = "good_appkey_constraint_test",
    fpga = fpga_params(
        changes_otp = True,
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --unlock-mode=Any
            --unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key)
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub)
            --config-kind=with-app-constraint
        """,
        test_harness = "//sw/host/tests/ownership:transfer_test",
    ),
    manifest = ":nodelocked_manifest",
)

# rom_ext_e2e_testplan.hjson%rom_ext_e2e_bad_unlock_test
ownership_transfer_test(
    name = "bad_unlock_test",
    fpga = fpga_params(
        changes_otp = True,
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --unlock-mode=Any
            # NOTE: We use the wrong unlock key to test that the unlock operation fails.
            --unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:activate_key)
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key)
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub)
            --expected-error=OwnershipInvalidSignature
        """,
        test_harness = "//sw/host/tests/ownership:transfer_test",
    ),
)

# rom_ext_e2e_testplan.hjson%rom_ext_e2e_bad_activate_test
ownership_transfer_test(
    name = "bad_activate_test",
    fpga = fpga_params(
        changes_otp = True,
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --unlock-mode=Any
            --unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            # NOTE: We use the wrong activate key to test that the activate operation fails.
            --activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key)
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub)
            --expected-error=OwnershipInvalidSignature
        """,
        test_harness = "//sw/host/tests/ownership:transfer_test",
    ),
)

# rom_ext_e2e_testplan.hjson%rom_ext_e2e_bad_owner_block_test
ownership_transfer_test(
    name = "bad_owner_block_test",
    fpga = fpga_params(
        changes_otp = True,
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --unlock-mode=Any
            --unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key)
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub)
            --config-kind=corrupt
            --dual-owner-boot-check=false
            --expected-error=OwnershipInvalidInfoPage
        """,
        test_harness = "//sw/host/tests/ownership:transfer_test",
    ),
)

# rom_ext_e2e_testplan.hjson%rom_ext_e2e_bad_app_key_test
ownership_transfer_test(
    name = "bad_app_key_test",
    fpga = fpga_params(
        changes_otp = True,
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --unlock-mode=Any
            --unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key)
            # NOTE: We use the wrong app key (fake instead of dummy) to test that we cannot boot
            # the test program after completing the transfer.
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa_pub)
            --expected-error=OwnershipKeyNotFound
        """,
        test_harness = "//sw/host/tests/ownership:transfer_test",
    ),
)

# rom_ext_e2e_testplan.hjson%rom_ext_e2e_transfer_endorsed_test
ownership_transfer_test(
    name = "transfer_endorsed_test",
    fpga = fpga_params(
        changes_otp = True,
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --unlock-mode=Endorsed
            --unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key)
            --next-owner-key-pub=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_pub)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key)
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub)
        """,
        test_harness = "//sw/host/tests/ownership:transfer_test",
    ),
)

# rom_ext_e2e_testplan.hjson%rom_ext_e2e_bad_endorsee_test
ownership_transfer_test(
    name = "bad_endorsee_test",
    fpga = fpga_params(
        changes_otp = True,
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --unlock-mode=Endorsed
            --unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key)
            # NOTE: We use the wrong next-owner-public-key to test that endorsee is rejected and the activate operation fails.
            --next-owner-key-pub=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:owner_key_pub)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key)
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub)
            --dual-owner-boot-check=false
            --expected-error=OwnershipInvalidInfoPage
        """,
        test_harness = "//sw/host/tests/ownership:transfer_test",
    ),
)

# rom_ext_e2e_testplan.hjson%rom_ext_e2e_locked_update_test
ownership_transfer_test(
    name = "locked_update_test",
    fpga = fpga_params(
        changes_otp = True,
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --unlock-mode=Update
            --unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:owner_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:activate_key)
            # NOTE: We rotate the `fake` test owner's application key to the dummy key to test that
            #       we can execute code with the new key.
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub)
            --non-transfer-update=true
        """,
        test_harness = "//sw/host/tests/ownership:transfer_test",
    ),
)

# rom_ext_e2e_testplan.hjson%rom_ext_e2e_bad_locked_update_test
# Part 1: Ensure in UnlockedSelf that a new owner key is rejected.
ownership_transfer_test(
    name = "bad_locked_update_test",
    ecdsa_key = {
        "//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa": "app_prod",
    },
    fpga = fpga_params(
        changes_otp = True,
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --unlock-mode=Update
            --unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            # NOTE: We use the wrong owner key to test that the activate operation fails.
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:activate_key)
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa_pub)
            --dual-owner-boot-check=false
            --expected-error=OwnershipInvalidInfoPage
        """,
        test_harness = "//sw/host/tests/ownership:transfer_test",
    ),
)

# rom_ext_e2e_testplan.hjson%rom_ext_e2e_bad_locked_update_test
# Part 2: Ensure the UnlockedSelf state denies execution to anything signed with new app keys.
ownership_transfer_test(
    name = "bad_locked_update_no_exec_test",
    fpga = fpga_params(
        changes_otp = True,
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --unlock-mode=Update
            --unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:activate_key)

            # NOTE: We use the wrong owner key and the dummy app key (which the ownership_transfer_test rule
            #       uses for signing) to check that owner code execution is denied in the intermediate
            #       dual-owner state.
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key)
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub)
            --expected-error=OwnershipKeyNotFound
        """,
        test_harness = "//sw/host/tests/ownership:transfer_test",
    ),
)

# rom_ext_e2e_testplan.hjson%rom_ext_e2e_rescue_limit_test
ownership_transfer_test(
    name = "rescue_limit_test",
    srcs = ["flash_contents.c"],
    fpga = fpga_params(
        timeout = "long",
        # We boot on Side B since rescue will rewrite side A.
        assemble = "{rom_ext}@0 {firmware}@0x90000",
        changes_otp = True,
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --unlock-mode=Any
            --unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key)
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub)
        """,
        test_harness = "//sw/host/tests/ownership:rescue_limit_test",
    ),
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_b",
    deps = [
        "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

# rom_ext_e2e_testplan.hjson%rom_ext_e2e_rescue_permission_test
ownership_transfer_test(
    name = "rescue_permission_test",
    fpga = fpga_params(
        changes_otp = True,
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --unlock-mode=Any
            --unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key)
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub)
        """,
        test_harness = "//sw/host/tests/ownership:rescue_permission_test",
    ),
)

# rom_ext_e2e_testplan.hjson%rom_ext_e2e_flash_permission_test
# Note: rescue-after-activate tests that rescue correctly accesses regions with
# different scrambling/ECC properties than the default flash configuration.
[
    ownership_transfer_test(
        name = "flash_permission_test_slot_{}".format(slot),
        srcs = ["flash_regions.c"],
        fpga = fpga_params(
            binaries = {
                ":flash_regions": "flash_regions",
            },
            slot = "Slot{}".format(slot.upper()),
            test_cmd = """
                --clear-bitstream
                --bootstrap={firmware}
                --unlock-mode=Any
                --unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
                --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key)
                --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key)
                --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key)
                --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub)
                --config-kind=with-flash-locked
                --rescue-after-activate={flash_regions}
                --rescue-slot={slot}
            """,
            test_harness = "//sw/host/tests/ownership:flash_permission_test",
        ),
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
        deps = [
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:status",
            "//sw/device/lib/dif:flash_ctrl",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for slot in ("a", "b")
]

# Tests that a owner config with an improper flash configuration cannot be activated.
ownership_transfer_test(
    name = "flash_error_test",
    fpga = fpga_params(
        changes_otp = True,
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --unlock-mode=Any
            --unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key)
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub)
            --config-kind=with-flash-error
            --dual-owner-boot-check=false
            --expected-error=OwnershipFlashConfigRomExt
        """,
        test_harness = "//sw/host/tests/ownership:transfer_test",
    ),
)

# Test that the `sku_creator_owner_init` function responsible for installing the test owner on
# FPGA builds will automatically update from an older owner block.
ownership_transfer_test(
    name = "fpga_owner_upgrade_test",
    ecdsa_key = {
        "//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa": "app_prod",
    },
    fpga = fpga_params(
        changes_otp = True,
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --unlock-mode=Update
            --unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:owner_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:activate_key)
            # `sku_creator_owner_init` has a newer version number than this and should self-update.
            --config-version=0
            # NOTE: Should sku_creator_owner_init fail to upgrade to its built-in owner block, then the
            # dummy key will prevent the test program from executing and we'll get a failure from the test.
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub)
            --non-transfer-update=true
        """,
        test_harness = "//sw/host/tests/ownership:transfer_test",
    ),
)

ownership_transfer_test(
    name = "newversion_update_test",
    ecdsa_key = {
        "//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa": "app_prod",
    },
    fpga = fpga_params(
        changes_otp = True,
        rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_owner_update_newversion",
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:owner_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:activate_key)
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa_pub)
            --config-version=2
            # We expect to see the version updated and the owner key the same.
            --expect "config_version = 2"
            --expect "owner_key = 8e3dcb50"
        """,
        test_harness = "//sw/host/tests/ownership:newversion_test",
    ),
)

ownership_transfer_test(
    name = "newversion_noupdate_test",
    ecdsa_key = {
        "//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa": "app_prod",
    },
    fpga = fpga_params(
        changes_otp = True,
        rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_owner_update_newversion",
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:owner_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:activate_key)
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa_pub)
            --config-version=0
            # We expect to see the version unchanged.
            --expect "config_version = 1"
            --expect "owner_key = 8e3dcb50"
        """,
        test_harness = "//sw/host/tests/ownership:newversion_test",
    ),
)

ownership_transfer_test(
    name = "newversion_nodelock_test",
    ecdsa_key = {
        "//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa": "app_prod",
    },
    fpga = fpga_params(
        changes_otp = True,
        rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_owner_update_newversion",
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:owner_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:activate_key)
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa_pub)
            --config-version=2
            # A DIN of zero will cause the test program to use the DUT's current DIN.
            --locked-to-din=0
            --expect "config_version = 2"
            --expect "owner_key = 8e3dcb50"
        """,
        test_harness = "//sw/host/tests/ownership:newversion_test",
    ),
)

ownership_transfer_test(
    name = "newversion_badlock_test",
    ecdsa_key = {
        "//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa": "app_prod",
    },
    fpga = fpga_params(
        changes_otp = True,
        rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_owner_update_newversion",
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:owner_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:activate_key)
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa_pub)
            --config-version=2
            --locked-to-din=12345
            # We expect to see the version unchanged.
            --expect "config_version = 1"
            --expect "owner_key = 8e3dcb50"
        """,
        test_harness = "//sw/host/tests/ownership:newversion_test",
    ),
)

opentitan_binary(
    name = "keymgr_test",
    testonly = True,
    srcs = ["//sw/device/silicon_creator/rom_ext/e2e/verified_boot:boot_test"],
    defines = [
        "WITH_OWNERSHIP_INFO=1",
        "WITH_KEYMGR=1",
    ],
    ecdsa_key = {
        "//sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa": "app_prod",
    },
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
    },
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/ownership:datatypes",
    ],
)

# rom_ext_e2e_testplan.hjson%rom_ext_e2e_transfer_any_test
ownership_transfer_test(
    name = "transfer_keymgr_test",
    srcs = ["//sw/device/silicon_creator/rom_ext/e2e/verified_boot:boot_test"],
    defines = [
        "WITH_OWNERSHIP_INFO=1",
        "WITH_KEYMGR=1",
    ],
    ecdsa_key = {
        "//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa": "app_prod",
    },
    fpga = fpga_params(
        binaries = {
            ":keymgr_test": "keymgr_test",
        },
        changes_otp = True,
        test_cmd = """
            --clear-bitstream
            --bootstrap={firmware}
            --pre-transfer-boot-check=true
            --unlock-mode=Any
            --unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/fake:unlock_key)
            --next-owner-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key)
            --next-unlock-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:unlock_key)
            --next-activate-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:activate_key)
            --next-application-key=$(location //sw/device/silicon_creator/lib/ownership/keys/dummy:app_prod_ecdsa_pub)
            --rescue-after-activate={keymgr_test}
            --keygen-check=true
        """,
        test_harness = "//sw/host/tests/ownership:transfer_test",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/ownership:datatypes",
    ],
)
