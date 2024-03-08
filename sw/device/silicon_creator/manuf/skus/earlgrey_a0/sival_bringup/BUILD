# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "opentitan_binary",
    "opentitan_test",
    "silicon_params",
)
load(
    "//sw/device/silicon_creator/manuf:provisioning_inputs.bzl",
    "CP_PROVISIONING_INPUTS",
    "EARLGREY_A0_INDIVIDUALIZE_OTP_SW_CFGS",
    "FT_PERSONALIZE_KEYS",
    "FT_PERSONALIZE_SIGNING_KEYS",
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
        "//sw/device/lib/base:abs_mmio",
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
        "//sw/device/silicon_creator/manuf/data/ast:fake",
        "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
        "//sw/device/silicon_creator/manuf/lib:individualize",
        "//sw/device/silicon_creator/manuf/lib:otp_fields",
        "//sw/device/silicon_creator/manuf/lib:sram_start_no_ast_init",
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
    cw310 = cw310_params(
        binaries = {":sram_cp_provision": "sram_cp_provision"},
        changes_otp = True,
        needs_jtag = True,
        otp = "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival_bringup:otp_img_test_unlocked0_manuf_empty",
        tags = ["manuf"],
        test_cmd = _CP_PROVISIONING_CMD_ARGS,
        test_harness = "//sw/host/tests/manuf/provisioning/cp",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:silicon_creator": None,
    },
    silicon = silicon_params(
        binaries = {":sram_cp_provision": "sram_cp_provision"},
        changes_otp = True,
        interface = "hyper310",
        needs_jtag = True,
        test_cmd = _CP_PROVISIONING_CMD_ARGS,
        test_harness = "//sw/host/tests/manuf/provisioning/cp",
    ),
)

opentitan_test(
    name = "cp_provision_functest",
    cw310 = cw310_params(
        binaries = {
            ":sram_cp_provision": "sram_cp_provision",
            ":sram_cp_provision_functest": "sram_cp_provision_functest",
        },
        bitstream = "//hw/bitstream:rom_with_fake_keys_otp_raw",
        changes_otp = True,
        needs_jtag = True,
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

[
    opentitan_binary(
        name = "sram_ft_individualize_{}".format(otp_sw_cfgs),
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
            "//sw/device/lib/dif:otp_ctrl",
            "//sw/device/lib/dif:pinmux",
            "//sw/device/lib/runtime:hart",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:flash_ctrl_testutils",
            "//sw/device/lib/testing:otp_ctrl_testutils",
            "//sw/device/lib/testing:pinmux_testutils",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_console",
            "//sw/device/lib/testing/test_framework:ottf_test_config",
            "//sw/device/lib/testing/test_framework:status",
            "//sw/device/lib/testing/test_framework:ujson_ottf",
            "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
            "//sw/device/silicon_creator/manuf/lib:individualize",
            "//sw/device/silicon_creator/manuf/lib:otp_fields",
            "//sw/device/silicon_creator/manuf/lib:sram_start",
            "//sw/device/silicon_creator/manuf/lib:individualize_sw_cfg_earlgrey_a0_sku_{}".format(otp_sw_cfgs),
        ],
    )
    for otp_sw_cfgs in EARLGREY_A0_INDIVIDUALIZE_OTP_SW_CFGS
]

filegroup(
    name = "sram_ft_individualize_all",
    testonly = True,
    srcs = [
        ":sram_ft_individualize_prodc",
        ":sram_ft_individualize_sival",
        ":sram_ft_individualize_sival_bringup",
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
    rsa_key = FT_PERSONALIZE_SIGNING_KEYS,
    deps = [
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:lc_ctrl_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/silicon_creator/manuf/lib:individualize_sw_cfg_earlgrey_a0_sku_sival_bringup",
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
    rsa_key = FT_PERSONALIZE_SIGNING_KEYS,
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
        "//sw/device/silicon_creator/lib/cert:cdi_0_template_library",
        "//sw/device/silicon_creator/lib/cert:cdi_1_template_library",
        "//sw/device/silicon_creator/lib/cert:dice",
        "//sw/device/silicon_creator/lib/cert:uds_template_library",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:keymgr",
        "//sw/device/silicon_creator/lib/drivers:kmac",
        "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
        "//sw/otbn/crypto:boot",
    ],
)

_FT_PROVISIONING_BINARIES = {
    ":sram_ft_individualize_sival_bringup": "sram_ft_individualize",
    ":ft_personalize_1": "ft_personalize_1",
    ":ft_personalize_3": "ft_personalize_3",
}

_FT_PROVISIONING_CMD_ARGS = """
  --elf={sram_ft_individualize}
  --bootstrap={ft_personalize_1}
  --third-bootstrap={ft_personalize_3}
""" + FT_PROVISIONING_INPUTS

opentitan_test(
    name = "ft_provision",
    cw310 = cw310_params(
        binaries = _FT_PROVISIONING_BINARIES,
        changes_otp = True,
        data = FT_PERSONALIZE_KEYS,
        needs_jtag = True,
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
    silicon = silicon_params(
        binaries = _FT_PROVISIONING_BINARIES,
        changes_otp = True,
        data = FT_PERSONALIZE_KEYS,
        interface = "hyper310",
        needs_jtag = True,
        test_cmd = _FT_PROVISIONING_CMD_ARGS,
        test_harness = "//sw/host/tests/manuf/provisioning/ft",
    ),
)
