# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:manifest.bzl", "CONST", "manifest")
load("//rules:opentitan.bzl", "opentitan_flash_binary")
load("//rules:linker.bzl", "ld_library")
load("//rules:cross_platform.bzl", "dual_cc_device_library_of", "dual_cc_library", "dual_inputs")

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
            "//sw/device/silicon_creator/testing:mask_rom_test",
            "@googletest//:gtest",
        ],
        shared = [
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
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest_main",
    ],
)

ld_library(
    name = "ld_common",
    fragments = ["rom_ext_common.ld"],
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
    name = "ld_virtual_addr",
    script = "rom_ext_virtual_addr.ld",
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
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/base:static_critical_boot_measurements",
        "//sw/device/silicon_creator/lib/base:static_critical_sec_mmio",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/drivers:pinmux",
        "//sw/device/silicon_creator/lib/drivers:uart",
        "//sw/device/silicon_creator/lib/sigverify",
        "//sw/device/silicon_creator/mask_rom:sigverify_keys",
    ],
)

manifest(
    name = "manifest_standard",
    address_translation = CONST.FALSE,
    identifier = CONST.ROM_EXT,
)

manifest(
    name = "manifest_virtual",
    address_translation = CONST.TRUE,
    identifier = CONST.ROM_EXT,
)

opentitan_flash_binary(
    name = "slot_a",
    srcs = ["rom_ext_start.S"],
    manifest = ":manifest_standard",
    output_signed = True,
    deps = [
        ":ld_slot_a",
        ":rom_ext",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

opentitan_flash_binary(
    name = "slot_b",
    srcs = ["rom_ext_start.S"],
    manifest = ":manifest_standard",
    output_signed = True,
    deps = [
        ":ld_slot_b",
        ":rom_ext",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

opentitan_flash_binary(
    name = "virtual_addr",
    srcs = ["rom_ext_start.S"],
    manifest = ":manifest_virtual",
    output_signed = True,
    deps = [
        ":ld_virtual_addr",
        ":rom_ext",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)
