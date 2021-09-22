# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

cc_library(
    name = "common",
    srcs = [
        "flash_crt.S",
        "ibex_interrupt_vectors.S",
    ],
    copts = [
        "-nostdlib",
        "-ffreestanding",
    ],
    linkopts = [
        "-T $(location flash_link.ld)",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "flash_link.ld",
        "//hw/top_earlgrey/sw/autogen:linker_script",
        "//sw/device:info_sections",
    ],
)
