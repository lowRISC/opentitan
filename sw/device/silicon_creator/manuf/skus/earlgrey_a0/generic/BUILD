# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan_test.bzl",
    "OPENTITANTOOL_OPENOCD_DATA_DEPS",
    "OPENTITANTOOL_OPENOCD_TEST_CMDS",
    "cw310_params",
    "opentitan_functest",
)
load(
    "//rules:opentitan.bzl",
    "RSA_ONLY_KEY_STRUCTS",
    "opentitan_ram_binary",
)

package(default_visibility = ["//visibility:public"])

opentitan_ram_binary(
    name = "sram_cp_provision_init",
    srcs = ["sram_cp_provision_init.c"],
    hdrs = ["sram_cp_provision_init.h"],
    archive_symbol_prefix = "sram_cp_provision_init",
    deps = [
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
        "//sw/device/lib/testing/json:provisioning_command",
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_console",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
        "//sw/device/silicon_creator/manuf/lib:individualize",
        "//sw/device/silicon_creator/manuf/lib:otp_fields",
        "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
        "//sw/device/silicon_creator/manuf/lib:sram_start",
    ],
)

opentitan_functest(
    name = "cp_provision_init",
    srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom_with_fake_keys_otp_raw",
        tags = ["manuf"],
        test_cmds = [
            "--clear-bitstream",
            "--bitstream=\"$(location {bitstream})\"",
            "--elf=\"$(rootpath :sram_cp_provision_init_fpga_cw310_elf_transition)\"",
            "--all-steps",
        ] + OPENTITANTOOL_OPENOCD_TEST_CMDS,
    ),
    data = [
        ":sram_cp_provision_init_fpga_cw310_elf_transition",
    ] + OPENTITANTOOL_OPENOCD_DATA_DEPS,
    key_struct = RSA_ONLY_KEY_STRUCTS[0],
    targets = ["cw310_rom_with_fake_keys"],
    test_harness = "//sw/host/tests/manuf/cp_provision_init",
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/sigverify:spx_verify",
    ],
)
