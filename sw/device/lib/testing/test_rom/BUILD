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
        "//sw/device/lib/base:mmio",
    ],
)

cc_library(
    name = "test_rom_lib",
    srcs = [
        "test_rom.c",
        "test_rom_start.S",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":bootstrap",
        ":chip_info",
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
        "//sw/device/lib:pinmux",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/crt",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing/test_framework",
        "//sw/device/silicon_creator/lib:manifest",
    ],
)

cc_library(
    name = "bootstrap",
    srcs = [
        "bootstrap.c",
    ],
    hdrs = [
        "bootstrap.h",
        "spiflash_frame.h",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:flash_ctrl",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework",
    ],
)

opentitan_functest(
    name = "test_rom_test",
    srcs = ["test_rom_test.c"],
)
