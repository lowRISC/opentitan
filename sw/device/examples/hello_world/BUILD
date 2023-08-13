# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU", "opentitan_flash_binary")
load("//rules:exclude_files.bzl", "exclude_files")
load("@rules_pkg//pkg:mappings.bzl", "pkg_files")

package(default_visibility = ["//visibility:public"])

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
        "//sw/lib/sw/device/base:mmio",
    ],
)

cc_library(
    name = "hello_world_lib",
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/examples:demos",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_start",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/crt",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:gpio",
        "//sw/top_darjeeling/sw/dif:pinmux",
        "//sw/top_darjeeling/sw/dif:spi_device",
        "//sw/top_darjeeling/sw/dif:uart",
    ],
)

exclude_files(
    name = "pre_package",
    testonly = True,
    srcs = [":hello_world"],
    exclude_suffix = [
        ".ll",
        ".i",
        ".s",
    ],
)

pkg_files(
    name = "package",
    testonly = True,
    srcs = [":pre_package"],
    prefix = "darjeeling/examples",
)
