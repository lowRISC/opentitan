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
    "silicon_jtag_params",
)
load(
    "//sw/device/silicon_creator/manuf/skus/earlgrey_a0/sival_bringup:provisioning_inputs.bzl",
    "CP_PROVISIONING_INPUTS",
    "FT_PROVISIONING_INPUTS",
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
        "//hw/top_earlgrey:silicon_creator": None,
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
        "//hw/top_earlgrey:silicon_creator": None,
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

_CP_PROVISIONING_CMD_ARGS = """
  --elf={sram_cp_provision}
""" + CP_PROVISIONING_INPUTS

opentitan_test(
    name = "cp_provision",
    cw310 = cw310_jtag_params(
        binaries = {":sram_cp_provision": "sram_cp_provision"},
        bitstream = "//hw/bitstream:rom_with_fake_keys_otp_raw",
        tags = ["manuf"],
        test_cmd = _CP_PROVISIONING_CMD_ARGS,
        test_harness = "//sw/host/tests/manuf/provisioning/cp",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:silicon_creator": None,
    },
    silicon = silicon_jtag_params(
        binaries = {":sram_cp_provision": "sram_cp_provision"},
        interface = "hyper310",
        test_cmd = _CP_PROVISIONING_CMD_ARGS,
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
        """ + CP_PROVISIONING_INPUTS,
        test_harness = "//sw/host/tests/manuf/provisioning/cp_test",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
)

opentitan_binary(
    name = "sram_ft_individualize",
    testonly = True,
    srcs = ["sram_ft_individualize.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:silicon_creator": None,
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
        "//sw/device/silicon_creator/manuf/lib:individualize",
        "//sw/device/silicon_creator/manuf/lib:individualize_sw_cfg_earlgrey_a0_sku_sival_bringup",
        "//sw/device/silicon_creator/manuf/lib:sram_start",
    ],
)

opentitan_binary(
    name = "ft_personalize_1",
    testonly = True,
    srcs = ["ft_personalize_1.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:silicon_creator": None,
    },
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
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
        "//sw/device/silicon_creator/manuf/lib:individualize_sw_cfg_earlgrey_a0_sku_sival_bringup",
        "//sw/device/silicon_creator/manuf/lib:personalize",
    ],
)

opentitan_binary(
    name = "ft_personalize_2",
    testonly = True,
    srcs = ["ft_personalize_2.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:silicon_creator": None,
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

opentitan_binary(
    name = "ft_personalize_3",
    testonly = True,
    srcs = ["ft_personalize_3.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:silicon_creator": None,
    },
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    rsa_key = rsa_key_for_lc_state(
        RSA_ONLY_KEY_STRUCTS,
        CONST.LCV.PROD,
    ),
    deps = [
        "//sw/device/lib/arch:device",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/silicon_creator/lib:attestation",
        "//sw/device/silicon_creator/lib:attestation_key_diversifiers",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:otbn_boot_services",
        "//sw/device/silicon_creator/lib/drivers:keymgr",
        "//sw/otbn/crypto:boot",
    ],
)

_FT_PROVISIONING_BINARIES = {
    ":sram_ft_individualize": "sram_ft_individualize",
    ":ft_personalize_1": "ft_personalize_1",
    ":ft_personalize_2": "ft_personalize_2",
    ":ft_personalize_3": "ft_personalize_3",
}

_FT_PROVISIONING_CMD_ARGS = """
  --elf={sram_ft_individualize}
  --bootstrap={ft_personalize_1}
  --second-bootstrap={ft_personalize_2}
  --third-bootstrap={ft_personalize_3}
""" + FT_PROVISIONING_INPUTS

opentitan_test(
    name = "ft_provision",
    cw310 = hyper310_jtag_params(
        binaries = _FT_PROVISIONING_BINARIES,
        data = ["//sw/device/silicon_creator/manuf/keys/fake:rma_unlock_token_export_key.sk_hsm.der"],
        otp = "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival_bringup:otp_img_test_locked0_manuf_initialized",
        tags = [
            "lc_test_locked0",
            "manuf",
        ],
        test_cmd = _FT_PROVISIONING_CMD_ARGS,
        test_harness = "//sw/host/tests/manuf/provisioning/ft",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:silicon_creator": None,
    },
    rsa_key = rsa_key_for_lc_state(
        RSA_ONLY_KEY_STRUCTS,
        CONST.LCV.PROD,
    ),
    silicon = silicon_jtag_params(
        binaries = _FT_PROVISIONING_BINARIES,
        data = ["//sw/device/silicon_creator/manuf/keys/fake:rma_unlock_token_export_key.sk_hsm.der"],
        interface = "hyper310",
        test_cmd = _FT_PROVISIONING_CMD_ARGS,
        test_harness = "//sw/host/tests/manuf/provisioning/ft",
    ),
)
