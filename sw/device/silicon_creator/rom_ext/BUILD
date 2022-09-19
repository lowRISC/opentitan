# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:manifest.bzl", "CONST", "manifest")
load("//rules:opentitan.bzl", "opentitan_flash_binary")
load("//rules:linker.bzl", "ld_library")
load("//rules:cross_platform.bzl", "dual_cc_library", "dual_inputs")
load("//rules:opentitan_test.bzl", "cw310_params", "opentitan_functest")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "rom_ext_epmp",
    srcs = ["rom_ext_epmp.c"],
    hdrs = ["rom_ext_epmp.h"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:csr",
        "//sw/device/silicon_creator/lib:epmp",
    ],
)

dual_cc_library(
    name = "rom_ext_boot_policy_ptrs",
    srcs = dual_inputs(
        host = ["mock_rom_ext_boot_policy_ptrs.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_rom_ext_boot_policy_ptrs.h"],
        shared = ["rom_ext_boot_policy_ptrs.h"],
    ),
    deps = dual_inputs(
        host = [
            "//sw/device/lib/base:global_mock",
            "//sw/device/silicon_creator/testing:rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            "//sw/device/silicon_creator/lib/base:chip",
            "//sw/device/lib/base:macros",
            "//sw/device/silicon_creator/lib:manifest",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        ],
    ),
)

cc_library(
    name = "rom_ext_boot_policy",
    srcs = ["rom_ext_boot_policy.c"],
    hdrs = ["rom_ext_boot_policy.h"],
    deps = [
        ":rom_ext_boot_policy_ptrs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:csr",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:manifest",
    ],
)

cc_test(
    name = "rom_ext_boot_policy_unittest",
    srcs = ["rom_ext_boot_policy_unittest.cc"],
    deps = [
        ":rom_ext_boot_policy",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

ld_library(
    name = "ld_common",
    includes = ["rom_ext_common.ld"],
    deps = [
        "//sw/device:info_sections",
        "//sw/device/silicon_creator/lib/base:static_critical_sections",
    ],
)

ld_library(
    name = "ld_slot_a",
    script = "rom_ext_slot_a.ld",
    deps = [
        ":ld_common",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
    ],
)

ld_library(
    name = "ld_slot_b",
    script = "rom_ext_slot_b.ld",
    deps = [
        ":ld_common",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
    ],
)

ld_library(
    name = "ld_slot_virtual",
    script = "rom_ext_slot_virtual.ld",
    deps = [
        ":ld_common",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
    ],
)

cc_library(
    name = "rom_ext",
    srcs = ["rom_ext.c"],
    hdrs = ["rom_ext.h"],
    deps = [
        ":rom_ext_boot_policy",
        ":rom_ext_epmp",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:stdasm",
        "//sw/device/lib/runtime:hart",
        "//sw/device/silicon_creator/lib:manifest",
        "//sw/device/silicon_creator/lib:manifest_def",
        "//sw/device/silicon_creator/lib:rom_print",
        "//sw/device/silicon_creator/lib:shutdown",
        "//sw/device/silicon_creator/lib/base:chip",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/base:static_critical_boot_measurements",
        "//sw/device/silicon_creator/lib/base:static_critical_sec_mmio",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:ibex",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/drivers:pinmux",
        "//sw/device/silicon_creator/lib/drivers:uart",
        "//sw/device/silicon_creator/lib/sigverify",
        "//sw/device/silicon_creator/rom:sigverify_keys",
    ],
)

manifest(
    name = "manifest_standard",
    address_translation = CONST.FALSE,
    identifier = CONST.ROM_EXT,
    visibility = ["//visibility:public"],
)

manifest(
    name = "manifest_virtual",
    address_translation = CONST.TRUE,
    identifier = CONST.ROM_EXT,
)

opentitan_flash_binary(
    name = "rom_ext_slot_a",
    srcs = ["rom_ext_start.S"],
    manifest = ":manifest_standard",
    signed = True,
    deps = [
        ":ld_slot_a",
        ":rom_ext",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

opentitan_flash_binary(
    name = "rom_ext_slot_b",
    srcs = ["rom_ext_start.S"],
    manifest = ":manifest_standard",
    signed = True,
    deps = [
        ":ld_slot_b",
        ":rom_ext",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

opentitan_flash_binary(
    name = "rom_ext_slot_virtual",
    srcs = ["rom_ext_start.S"],
    manifest = ":manifest_virtual",
    signed = True,
    deps = [
        ":ld_slot_virtual",
        ":rom_ext",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

BOOT_SUCCESS_MSG = "Starting ROM_EXT"

opentitan_functest(
    name = "rom_ext_slot_a_boot_test",
    cw310 = cw310_params(
        exit_success = BOOT_SUCCESS_MSG,
    ),
    ot_flash_binary = ":rom_ext_slot_a",
    signed = True,
    targets = ["cw310_rom"],
)

# TODO(#13511): Add a positive test for slot_b.

opentitan_functest(
    name = "rom_ext_slot_virtual_boot_test",
    cw310 = cw310_params(
        exit_success = BOOT_SUCCESS_MSG,
    ),
    ot_flash_binary = ":rom_ext_slot_virtual",
    signed = True,
    targets = ["cw310_rom"],
)
