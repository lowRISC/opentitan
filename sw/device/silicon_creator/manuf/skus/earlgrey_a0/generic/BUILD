# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST")
load(
    "//rules:opentitan.bzl",
    "RSA_ONLY_KEY_STRUCTS",
)
load(
    "//rules/opentitan:defs.bzl",
    "cw310_jtag_params",
    "hyper310_jtag_params",
    "opentitan_binary",
    "opentitan_test",
    "rsa_key_for_lc_state",
)

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "flash_info_permissions",
    srcs = ["flash_info_permissions.h"],
    deps = ["//sw/device/lib/dif:flash_ctrl"],
)

opentitan_binary(
    name = "sram_cp_provision",
    testonly = True,
    srcs = ["sram_cp_provision.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    kind = "ram",
    linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
    deps = [
        ":flash_info_permissions",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:lc_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_console",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
        "//sw/device/silicon_creator/manuf/lib:individualize",
        "//sw/device/silicon_creator/manuf/lib:otp_fields",
        "//sw/device/silicon_creator/manuf/lib:sram_start",
    ],
)

opentitan_binary(
    name = "sram_cp_provision_functest",
    testonly = True,
    srcs = ["sram_cp_provision_functest.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    kind = "ram",
    linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
    deps = [
        ":flash_info_permissions",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:lc_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_console",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
        "//sw/device/silicon_creator/manuf/lib:individualize",
        "//sw/device/silicon_creator/manuf/lib:otp_fields",
        "//sw/device/silicon_creator/manuf/lib:sram_start",
    ],
)

opentitan_test(
    name = "cp_provision",
    cw310 = cw310_jtag_params(
        binaries = {
            ":sram_cp_provision": "sram_cp_provision",
        },
        bitstream = "//hw/bitstream:rom_with_fake_keys_otp_raw",
        tags = ["manuf"],
        test_cmd = """
            --elf={sram_cp_provision}
        """,
        test_harness = "//sw/host/tests/manuf/provisioning/cp",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
    },
    hyper310 = hyper310_jtag_params(
        binaries = {
            ":sram_cp_provision": "sram_cp_provision",
        },
        bitstream = "//hw/bitstream/hyperdebug:rom_with_fake_keys_otp_raw",
        tags = ["manuf"],
        test_cmd = """
            --elf={sram_cp_provision}
        """,
        test_harness = "//sw/host/tests/manuf/provisioning/cp",
    ),
)

opentitan_test(
    name = "cp_provision_functest",
    cw310 = cw310_jtag_params(
        binaries = {
            ":sram_cp_provision": "sram_cp_provision",
            ":sram_cp_provision_functest": "sram_cp_provision_functest",
        },
        bitstream = "//hw/bitstream:rom_with_fake_keys_otp_raw",
        tags = ["manuf"],
        test_cmd = """
            --provisioning-sram-elf={sram_cp_provision}
            --test-sram-elf={sram_cp_provision_functest}
        """,
        test_harness = "//sw/host/tests/manuf/provisioning/cp_test",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
    },
    hyper310 = hyper310_jtag_params(
        binaries = {
            ":sram_cp_provision": "sram_cp_provision",
            ":sram_cp_provision_functest": "sram_cp_provision_functest",
        },
        bitstream = "//hw/bitstream/hyperdebug:rom_with_fake_keys_otp_raw",
        tags = ["manuf"],
        test_cmd = """
            --provisioning-sram-elf={sram_cp_provision}
            --test-sram-elf={sram_cp_provision_functest}
        """,
        test_harness = "//sw/host/tests/manuf/provisioning/cp_test",
    ),
)

opentitan_binary(
    name = "sram_ft_individualize",
    testonly = True,
    srcs = ["sram_ft_individualize.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    kind = "ram",
    linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
    deps = [
        ":flash_info_permissions",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:lc_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_console",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
        "//sw/device/silicon_creator/manuf/lib:individualize",
        "//sw/device/silicon_creator/manuf/lib:individualize_sw_cfg_earlgrey_a0_sku_generic",
        "//sw/device/silicon_creator/manuf/lib:otp_fields",
        "//sw/device/silicon_creator/manuf/lib:sram_start",
    ],
)

opentitan_binary(
    name = "ft_personalize_2",
    testonly = True,
    srcs = ["ft_personalize_2.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    rsa_key = rsa_key_for_lc_state(
        RSA_ONLY_KEY_STRUCTS,
        CONST.LCV.PROD,
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/silicon_creator/manuf/lib:personalize",
    ],
)

opentitan_test(
    name = "ft_provision",
    srcs = ["ft_personalize_1.c"],
    cw310 = cw310_jtag_params(
        binaries = {
            ":sram_ft_individualize": "sram_ft_individualize",
            ":ft_personalize_2": "ft_personalize_2",
        },
        bitstream = "//hw/bitstream:rom_with_fake_keys_otp_sival_test_locked0",
        data = ["//sw/device/silicon_creator/manuf/keys/fake:rma_unlock_token_export_key.sk_hsm.der"],
        tags = ["manuf"],
        test_cmd = """
            --elf={sram_ft_individualize}
            --bootstrap={firmware}
            --second-bootstrap={ft_personalize_2}
            --target-mission-mode-lc-state="prod"
            --host-ecc-sk="$(rootpath //sw/device/silicon_creator/manuf/keys/fake:rma_unlock_token_export_key.sk_hsm.der)"
        """,
        test_harness = "//sw/host/tests/manuf/provisioning/ft",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
    },
    hyper310 = hyper310_jtag_params(
        binaries = {
            ":sram_ft_individualize": "sram_ft_individualize",
            ":ft_personalize_2": "ft_personalize_2",
        },
        bitstream = "//hw/bitstream/hyperdebug:rom_with_fake_keys_otp_sival_test_locked0",
        data = ["//sw/device/silicon_creator/manuf/keys/fake:rma_unlock_token_export_key.sk_hsm.der"],
        tags = ["manuf"],
        test_cmd = """
            --elf={sram_ft_individualize}
            --bootstrap={firmware}
            --second-bootstrap={ft_personalize_2}
            --target-mission-mode-lc-state="prod"
            --host-ecc-sk="$(rootpath //sw/device/silicon_creator/manuf/keys/fake:rma_unlock_token_export_key.sk_hsm.der)"
        """,
        test_harness = "//sw/host/tests/manuf/provisioning/ft",
    ),
    rsa_key = rsa_key_for_lc_state(
        RSA_ONLY_KEY_STRUCTS,
        CONST.LCV.PROD,
    ),
    deps = [
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:lc_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/manuf/lib:individualize_sw_cfg_earlgrey_a0_sku_generic",
        "//sw/device/silicon_creator/manuf/lib:personalize",
    ],
)
