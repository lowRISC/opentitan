# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "opentitan_flash_binary")
load("//rules:linker.bzl", "ld_library")

ld_library(
    name = "ld_common",
    fragments = ["bare_metal_common.ld"],
    deps = [
        "//sw/device:info_sections",
        "//sw/device/silicon_creator/lib/base:static_critical_sections",
    ],
)

ld_library(
    name = "ld_slot_a",
    script = "bare_metal_slot_a.ld",
    deps = [
        ":ld_common",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
    ],
)

ld_library(
    name = "ld_slot_b",
    script = "bare_metal_slot_b.ld",
    deps = [
        ":ld_common",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
    ],
)

ld_library(
    name = "ld_virtual_addr",
    script = "bare_metal_virtual_addr.ld",
    deps = [
        ":ld_common",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
    ],
)

cc_library(
    name = "bare_metal_example",
    srcs = ["bare_metal_example.c"],
    hdrs = ["bare_metal_example.h"],
    deps = [
        "//sw/device/silicon_creator/lib:manifest_def",
        "//sw/device/silicon_creator/lib:rom_print",
    ],
)

opentitan_flash_binary(
    name = "bare_metal_example_slot_a",
    srcs = ["bare_metal_start.S"],
    deps = [
        ":bare_metal_example",
        ":ld_slot_a",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

opentitan_flash_binary(
    name = "bare_metal_example_slot_b",
    srcs = ["bare_metal_start.S"],
    deps = [
        ":bare_metal_example",
        ":ld_slot_b",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

opentitan_flash_binary(
    name = "bare_metal_example_virtual_addr",
    srcs = ["bare_metal_start.S"],
    deps = [
        ":bare_metal_example",
        ":ld_virtual_addr",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)
