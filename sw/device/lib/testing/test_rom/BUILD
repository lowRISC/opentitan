# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU", "opentitan_rom_binary")
load("//rules:opentitan_test.bzl", "opentitan_functest")
load("//rules:autogen.bzl", "autogen_chip_info")
load("//rules:linker.bzl", "ld_library")

package(default_visibility = ["//visibility:public"])

autogen_chip_info(
    name = "chip_info",
)

ld_library(
    name = "linker_script",
    script = "test_rom.ld",
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
        "//sw/device:info_sections",
    ],
)

opentitan_rom_binary(
    name = "test_rom",
    deps = [
        ":linker_script",
        ":test_rom_lib",
    ],
)

# TODO(#12905): Use a slightly hollowed out version of the silicon_creator bootstrap
# implemention when building the test_rom for the english breakfast top level.
cc_library(
    name = "english_breakfast_test_rom_bootstrap",
    srcs = [
        "english_breakfast_fake_driver_funcs.c",
        "//sw/device/silicon_creator/lib/drivers:english_breakfast_test_rom_driver_srcs",
        "//sw/device/silicon_creator/mask_rom:english_breakfast_test_rom_bootstrap_srcs",
    ],
    # This should be built only for english breakfast and skipped if using wildcards.
    tags = ["manual"],
    deps = [
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//hw/ip/gpio/data:gpio_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/spi_device/data:spi_device_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

alias(
    name = "test_rom_bootstrap",
    actual = select({
        "//sw/device:is_english_breakfast": ":english_breakfast_test_rom_bootstrap",
        "//conditions:default": "//sw/device/silicon_creator/mask_rom:bootstrap",
    }),
    visibility = ["//visibility:private"],
)

# TODO(#12905): Use a slightly hollowed out version of the silicon_creator manifest
# implementation when building the test_rom for the english breakfast top level.
cc_library(
    name = "english_breakfast_test_rom_manifest",
    srcs = [
        "//sw/device/silicon_creator/lib:english_breakfast_test_rom_manifest_srcs",
        "//sw/device/silicon_creator/lib/drivers:english_breakfast_test_rom_driver_srcs",
    ],
    # This should be built only for english breakfast and skipped if using wildcards.
    tags = ["manual"],
    deps = [
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/spi_device/data:spi_device_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:multibits",
        "//sw/device/silicon_creator/lib:epmp",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:keymgr_binding",
        "//sw/device/silicon_creator/lib:manifest_size",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/sigverify:rsa_key",
    ],
)

alias(
    name = "test_rom_manifest",
    actual = select({
        "//sw/device:is_english_breakfast": ":english_breakfast_test_rom_manifest",
        "//conditions:default": "//sw/device/silicon_creator/lib:manifest",
    }),
    visibility = ["//visibility:private"],
)

cc_library(
    name = "test_rom_lib",
    srcs = [
        "test_rom.c",
        "test_rom_start.S",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":chip_info",
        ":test_rom_bootstrap",
        ":test_rom_manifest",
        "//hw/ip/clkmgr/data:clkmgr_regs",
        "//hw/ip/csrng/data:csrng_regs",
        "//hw/ip/edn/data:edn_regs",
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//hw/top_earlgrey/ip/ast/data:ast_regs",
        "//hw/top_earlgrey/ip/sensor_ctrl/data:sensor_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:ibex_peri",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/crt",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:status",
    ],
)

opentitan_functest(
    name = "test_rom_test",
    srcs = ["test_rom_test.c"],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
