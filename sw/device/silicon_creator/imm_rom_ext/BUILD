# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@lowrisc_opentitan//rules/opentitan:transform.bzl", "obj_transform")
load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU", "opentitan_binary")
load("//rules:linker.bzl", "ld_library")
load("//sw/device/silicon_creator/imm_rom_ext:utils.bzl", "imm_rom_ext_section")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "main_lib",
    srcs = ["imm_rom_ext.c"],
    hdrs = ["imm_rom_ext.h"],
)

ld_library(
    name = "ld_hello_world",
    script = "hello_world.ld",
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
        "//sw/device:info_sections",
    ],
)

cc_library(
    name = "hello_world",
    srcs = [
        "hello_world.c",
        "hello_world_start.S",
    ],
    hdrs = ["hello_world.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/silicon_creator/lib/drivers:uart",
    ],
)

opentitan_binary(
    name = "hello_world_binaries",
    # TODO(#24368): Support multiple executing environments. Currently all
    # environments derive the same binary so only one environment is kept here,
    # but we need to support multiple executing environments and make sure
    # ROM_EXT targets choose the matched environment when linking IMM_ROM_EXT.
    exec_env = [
        "//hw/top_earlgrey:fpga_cw340",
    ],
    linker_script = ":ld_hello_world",
    deps = [
        ":hello_world",
    ],
)

imm_rom_ext_section(
    name = "hello_world_section",
    srcs = [":hello_world_binaries"],
)
