# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "OPENTITAN_CPU", "opentitan_binary", "opentitan_functest")
load("//rules:autogen.bzl", "autogen_chip_info")

autogen_chip_info(
    name = "chip_info",
)

opentitan_binary(
    name = "boot_rom",
    srcs = [
        "irq_vector.S",
    ],
    linkopts = [
        "-T $(location rom_link.ld)",
    ],
    output_scrambled = True,
    deps = [
        "rom_link.ld",
        ":boot_rom_lib",
        "//sw/device/lib/base:mmio",
    ],
)

cc_library(
    name = "boot_rom_lib",
    srcs = [
        "boot_rom.c",
        "rom_crt.S",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":bootstrap",
        ":chip_info",
        "//hw/ip/csrng/data:csrng_regs",
        "//hw/ip/edn/data:edn_regs",
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:linker_script",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device:info_sections",
        "//sw/device/lib:ibex_peri",
        "//sw/device/lib:pinmux",
        "//sw/device/lib/base",
        "//sw/device/lib/crt",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing/test_framework",
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
        "//sw/device/lib/base",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework",
    ],
)

opentitan_functest(
    name = "boot_rom_test",
    srcs = [
        "boot_rom_test.c",
    ],
    deps = [
    ],
)
