# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:defs.bzl", "opentitan_binary")
load("//rules:linker.bzl", "ld_library")

package(default_visibility = ["//visibility:public"])

ld_library(
    name = "sram_program_linker_script",
    # We want to avoid page alignment since the SRAM program is not loaded at the beginning of the
    # SRAM and the generated ELF segment should not contain any headers (as this could overwrite
    # some SRAM content)
    non_page_aligned_segments = True,
    script = "sram_program.ld",
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
        "//sw/device:info_sections",
        "//sw/device/silicon_creator/lib/base:static_critical_sections",
    ],
)

opentitan_binary(
    name = "sram_program",
    testonly = True,
    srcs = ["sram_program.c"],
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310_test_rom",
        "//hw/top_earlgrey:sim_dv",
        "//hw/top_earlgrey:sim_verilator",
    ],
    kind = "ram",
    linker_script = ":sram_program_linker_script",
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:status",
    ],
)
