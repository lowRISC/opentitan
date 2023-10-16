# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otp.bzl", "otp_image")
load("//rules:splice.bzl", "bitstream_splice")
load(
    "//rules/opentitan:defs.bzl",
    "cw310_jtag_params",
    "opentitan_binary",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

opentitan_binary(
    name = "sram_cp_provision",
    testonly = True,
    srcs = [
        "consts.h",
        "sram_cp_provision.c",
    ],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    kind = "ram",
    linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
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
        "//sw/device/silicon_creator/manuf/lib:sram_start",
    ],
)

opentitan_binary(
    name = "sram_cp_provision_functest",
    testonly = True,
    srcs = [
        "consts.h",
        "sram_cp_provision_functest.c",
    ],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    kind = "ram",
    linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
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
            --all-steps
        """,
        test_harness = "//sw/host/tests/manuf/provisioning/cp",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
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
            --all-steps
        """,
        test_harness = "//sw/host/tests/manuf/provisioning/cp_test",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
)

opentitan_binary(
    name = "sram_ft_provision",
    testonly = True,
    srcs = ["sram_ft_provision.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    kind = "ram",
    linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
    deps = [
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
        "//sw/device/lib/testing/json:provisioning_command",
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

# This is the same as //hw/ip/otp_ctrl/data:img_test_locked* but with *_SW_CFG
# partitions unprovisioned (and as a result, ROM execution also disabled).
otp_image(
    name = "otp_img_post_cp_test_locked0",
    src = "//hw/ip/otp_ctrl/data:otp_json_test_locked0",
    overlays = ["//hw/ip/otp_ctrl/data:otp_json_fixed_secret0"],
    visibility = ["//visibility:private"],
)

bitstream_splice(
    name = "bitstream_post_cp_test_locked0",
    src = "//hw/bitstream:rom_with_fake_keys",
    data = ":otp_img_post_cp_test_locked0",
    meminfo = "//hw/bitstream:otp_mmi",
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

opentitan_test(
    name = "ft_provision",
    cw310 = cw310_jtag_params(
        binaries = {
            ":sram_ft_provision": "sram_ft_provision",
        },
        bitstream = ":bitstream_post_cp_test_locked0",
        tags = ["manuf"],
        test_cmd = """
            --elf={sram_ft_provision}
            --all-steps
        """,
        test_harness = "//sw/host/tests/manuf/provisioning/ft",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
)
