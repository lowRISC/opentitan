# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU", "opentitan_ram_binary")
load("//rules:exclude_files.bzl", "exclude_files")
load("//rules:linker.bzl", "ld_library")
load(
    "//rules:opentitan_test.bzl",
    "manual_test",
    "opentitan_functest",
)
load("//rules:cross_platform.bzl", "dual_cc_library", "dual_inputs")
load("@rules_pkg//pkg:mappings.bzl", "pkg_files")

package(default_visibility = ["//visibility:public"])

opentitan_ram_binary(
    name = "hello_world",
    srcs = [
    	"hello_world.c",
    ],
    hdrs = [
        "hello_world.h",
    ],

    archive_symbol_prefix = "hello_world",
    testonly = True,
    deps = [
        "//hw/top_earlgrey/sw/tests/common:common",
        "//hw/top_earlgrey/sw/tests/common:linker",
        "//hw/top_earlgrey/sw/tests/common:crt",
	"//sw/device/silicon_creator/rom:rom_common",
     ],
)