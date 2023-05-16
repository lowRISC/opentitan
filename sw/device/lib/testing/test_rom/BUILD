# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU", "opentitan_rom_binary")
load("//rules:opentitan_test.bzl", "opentitan_functest")
load("//rules:exclude_files.bzl", "exclude_files")
load("//rules:linker.bzl", "ld_library")
load("@rules_pkg//pkg:mappings.bzl", "pkg_files")

package(default_visibility = ["//visibility:public"])

ld_library(
    name = "linker_script",
    script = "test_rom.ld",
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
        "//sw/device:info_sections",
        "//sw/device/silicon_creator/lib/base:static_critical_sections",
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
# and other functions necessary to build the test_rom for the english breakfast top level.
cc_library(
    name = "english_breakfast_test_rom_lib",
    srcs = [
        "english_breakfast_fake_driver_funcs.c",
        "//sw/device/silicon_creator/lib/drivers:english_breakfast_test_rom_driver_srcs",
        "//sw/device/silicon_creator/rom:english_breakfast_test_rom_bootstrap_srcs",
    ],
    # This should be built only for english breakfast and skipped if using wildcards.
    tags = ["manual"],
    deps = [
        "//hw/ip/gpio/data:gpio_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/spi_device/data:spi_device_regs",
        "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/dif:rstmgr_intf",
        "//sw/device/silicon_creator/lib/base:chip",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

cc_library(
    name = "earl_grey_test_rom_lib",
    deps = [
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/rom:bootstrap",
    ],
)

alias(
    name = "target_test_rom_lib",
    actual = select({
        "//sw/device:is_english_breakfast": ":english_breakfast_test_rom_lib",
        "//conditions:default": ":earl_grey_test_rom_lib",
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
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/spi_device/data:spi_device_regs",
        "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:multibits",
        "//sw/device/silicon_creator/lib:epmp_state",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:keymgr_binding",
        "//sw/device/silicon_creator/lib/base:chip",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/sigverify:rsa_key",
        "//sw/device/silicon_creator/lib/sigverify:spx_key",
    ],
)

alias(
    name = "test_rom_manifest",
    actual = select({
        "//sw/device:is_english_breakfast": ":english_breakfast_test_rom_manifest",
        "//conditions:default": "//sw/device/silicon_creator/lib:manifest",
    }),
)

cc_library(
    name = "test_rom_lib",
    srcs = [
        "test_rom.c",
        "test_rom_start.S",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":target_test_rom_lib",
        ":test_rom_manifest",
        "//hw/ip/csrng/data:csrng_regs",
        "//hw/ip/edn/data:edn_regs",
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//hw/top_earlgrey/ip/ast/data:ast_regs",
        "//hw/top_earlgrey/ip/clkmgr/data/autogen:clkmgr_regs",
        "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//hw/top_earlgrey/ip/sensor_ctrl/data:sensor_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/crt",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/silicon_creator/lib:chip_info",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/base:static_critical_boot_measurements",
        "//sw/device/silicon_creator/lib/base:static_critical_epmp_state",
        "//sw/device/silicon_creator/lib/base:static_critical_sec_mmio",
    ],
)

opentitan_functest(
    name = "test_rom_test",
    srcs = ["test_rom_test.c"],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

exclude_files(
    name = "pre_package",
    testonly = True,
    srcs = [":test_rom"],
    exclude_suffix = [
        ".ll",
        ".i",
        ".s",
    ],
)

pkg_files(
    name = "package",
    testonly = True,
    srcs = [":pre_package"],
    prefix = "earlgrey/test_rom",
)
