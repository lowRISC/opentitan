# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU", "opentitan_flash_binary")

opentitan_flash_binary(
    name = "hello_world",
    srcs = [
        "hello_world.c",
    ],
    copts = [
        "-nostdlib",
        "-ffreestanding",
        # Disable the date-time warning only for the hello world program.
        "-Wno-date-time",
    ],
    deps = [
        ":hello_world_lib",
        "//sw/device/lib/base:mmio",
    ],
)

cc_library(
    name = "hello_world_lib",
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/examples:demos",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/crt",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_start",
    ],
)
