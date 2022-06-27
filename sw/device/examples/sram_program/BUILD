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
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
        "//sw/device:info_sections",
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
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:sram_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
    ],
)
