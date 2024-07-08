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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling_memory",
        "//sw/device:info_sections",
        "//sw/lib/sw/device/silicon_creator/base:static_critical_sections",
    ],
)

ld_library(
    name = "second_rom_linker_script",
    script = "test_second_rom.ld",
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling_memory",
        "//sw/device:info_sections",
        "//sw/lib/sw/device/silicon_creator/base:static_critical_sections",
    ],
)

opentitan_rom_binary(
    name = "test_rom",
    mode = "base-rom",
    deps = [
        ":linker_script",
        ":test_rom_lib",
    ],
)

opentitan_rom_binary(
    name = "test_second_rom",
    mode = "second-rom",
    deps = [
        ":second_rom_linker_script",
        ":test_second_rom_lib",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:multibits",
        "//sw/lib/sw/device/silicon_creator/base:chip",
        "//sw/lib/sw/device/silicon_creator/base:sec_mmio",
        "//sw/top_darjeeling/sw/dif:rstmgr_intf",
    ],
)

cc_library(
    name = "earl_grey_test_rom_lib",
    deps = [
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/top_darjeeling/sw/dif:rstmgr",
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
        "//sw/device/silicon_creator/lib/drivers:english_breakfast_test_rom_driver_srcs",
        "//sw/top_darjeeling/sw/device/silicon_creator:english_breakfast_test_rom_manifest_srcs",
    ],
    # This should be built only for english breakfast and skipped if using wildcards.
    tags = ["manual"],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/spi_device/data:spi_device_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:multibits",
        "//sw/lib/sw/device/silicon_creator:epmp_state",
        "//sw/lib/sw/device/silicon_creator:error",
        "//sw/lib/sw/device/silicon_creator:keymgr_binding",
        "//sw/lib/sw/device/silicon_creator/base:chip",
        "//sw/lib/sw/device/silicon_creator/base:sec_mmio",
        "//sw/lib/sw/device/silicon_creator/sigverify:ecdsa_p256_key",
        "//sw/lib/sw/device/silicon_creator/sigverify:rsa_key",
        "//sw/lib/sw/device/silicon_creator/sigverify:spx_key",
    ],
)

alias(
    name = "test_rom_manifest",
    actual = select({
        "//sw/device:is_english_breakfast": ":english_breakfast_test_rom_manifest",
        "//conditions:default": "//sw/top_darjeeling/sw/device/silicon_creator:manifest",
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
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//hw/top_darjeeling/ip/ast/data:ast_regs",
        "//hw/top_darjeeling/ip/clkmgr/data/autogen:clkmgr_regs",
        "//hw/top_darjeeling/ip/sensor_ctrl/data:sensor_ctrl_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/crt",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:log",
        "//sw/lib/sw/device/silicon_creator/base:sec_mmio",
        "//sw/lib/sw/device/silicon_creator/base:static_critical",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/device/silicon_creator:chip_info",
        "//sw/top_darjeeling/sw/dif:clkmgr",
        "//sw/top_darjeeling/sw/dif:gpio",
        "//sw/top_darjeeling/sw/dif:hmac",
        "//sw/top_darjeeling/sw/dif:pinmux",
        "//sw/top_darjeeling/sw/dif:rv_core_ibex",
        "//sw/top_darjeeling/sw/dif:spi_device",
        "//sw/top_darjeeling/sw/dif:uart",
        "//sw/top_darjeeling/sw/test/utils:pinmux_testutils",
    ],
)

cc_library(
    name = "test_second_rom_lib",
    srcs = [
        "test_second_rom.c",
        "test_second_rom_start.S",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":test_rom_manifest",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//hw/top_darjeeling/ip/clkmgr/data/autogen:clkmgr_regs",
        "//hw/top_darjeeling/ip/sensor_ctrl/data:sensor_ctrl_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/crt",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:log",
        "//sw/lib/sw/device/silicon_creator/base:sec_mmio",
        "//sw/lib/sw/device/silicon_creator/base:static_critical",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/device/silicon_creator:chip_info",
        "//sw/top_darjeeling/sw/dif:clkmgr",
        "//sw/top_darjeeling/sw/dif:gpio",
        "//sw/top_darjeeling/sw/dif:pinmux",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/dif:rv_core_ibex",
        "//sw/top_darjeeling/sw/dif:uart",
        "//sw/top_darjeeling/sw/test/utils:pinmux_testutils",
    ],
)

opentitan_functest(
    name = "test_rom_test",
    srcs = ["test_rom_test.c"],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/top_darjeeling/sw/device/runtime:print",
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
    prefix = "darjeeling/test_rom",
)
