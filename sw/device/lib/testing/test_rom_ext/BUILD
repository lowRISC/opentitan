# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "test_rom_ext",
    srcs = [
        "test_rom_ext_irq_vector.S",
        "test_rom_ext_start.S",
    ],
    copts = [
        "-nostdlib",
        "-ffreestanding",
    ],
    linkopts = [
        "-T $(location test_rom_ext.ld)",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "test_rom_ext.ld",
        "//hw/top_earlgrey/sw/autogen:linker_script",
        "//sw/device:info_sections",
        "//sw/device/lib/crt",
        "//sw/device/lib/testing/test_framework:ottf_isrs",
    ],
)
