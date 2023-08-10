# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "opentitan_ram_binary")
load("//rules:linker.bzl", "ld_library")

package(default_visibility = ["//visibility:public"])

ld_library(
    name = "sram_program_linker_script",
    script = "sram_program.ld",
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling_memory",
        "//sw/device:info_sections",
        "//sw/lib/sw/device/silicon_creator/base:static_critical_sections",
    ],
)

opentitan_ram_binary(
    name = "sram_program",
    srcs = [
        "sram_program.c",
    ],
    hdrs = [
        "sram_program.h",
    ],
    archive_symbol_prefix = "sram_program",
    deps = [
        ":sram_program_linker_script",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/test/utils:pinmux_testutils",
    ],
)
