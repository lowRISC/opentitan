# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:manifest.bzl", "CONST", "manifest")
load("//rules:opentitan.bzl", "opentitan_flash_binary")
load("//rules:linker.bzl", "ld_library")
load("//rules:opentitan_test.bzl", "cw310_params", "opentitan_functest")

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

manifest(
    name = "manifest_standard",
    address_translation = CONST.FALSE,
    identifier = CONST.OWNER,
)

manifest(
    name = "manifest_virtual",
    address_translation = CONST.TRUE,
    identifier = CONST.OWNER,
)

opentitan_flash_binary(
    name = "bare_metal_example_slot_a",
    srcs = ["bare_metal_start.S"],
    manifest = ":manifest_standard",
    signed = True,
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
    manifest = ":manifest_standard",
    signed = True,
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
    manifest = ":manifest_virtual",
    signed = True,
    deps = [
        ":bare_metal_example",
        ":ld_virtual_addr",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

# TODO(#13511): This is a temporary workaround until #13511 is resolved.
genrule(
    name = "rom_ext_virt_a_owner_virt_a_fpga_cw310_bin_signed_test_key_0",
    srcs = [
        "//sw/device/silicon_creator/rom_ext:virtual_addr_fpga_cw310_bin_signed_test_key_0",
        ":bare_metal_example_virtual_addr_fpga_cw310_bin_signed_test_key_0",
    ],
    outs = ["rom_ext_virt_a_owner_virt_a_fpga_cw310.test_key_0.signed.bin"],
    cmd = "./$(location //sw/host/opentitantool) image assemble --mirror false --output $@ --size 0x11000 " +
          "$(location //sw/device/silicon_creator/rom_ext:virtual_addr_fpga_cw310_bin_signed_test_key_0)@0 " +
          "$(location :bare_metal_example_virtual_addr_fpga_cw310_bin_signed_test_key_0)@0x10000",
    tools = ["//sw/host/opentitantool"],
)

filegroup(
    name = "rom_ext_virt_a_owner_virt_a_fpga_cw310",
    srcs = [":rom_ext_virt_a_owner_virt_a"],
)

filegroup(
    name = "rom_ext_virt_a_owner_virt_a",
    srcs = ["rom_ext_virt_a_owner_virt_a_fpga_cw310.test_key_0.signed.bin"],
)

BOOT_SUCCESS_MSG = "Bare metal PASS!"

BOOT_FAILURE_MSG = "BFV:[0-9a-f]{8}"

opentitan_functest(
    name = "e2e_rom_ext_virt_a_owner_virt_a",
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom",
        exit_failure = BOOT_FAILURE_MSG,
        exit_success = BOOT_SUCCESS_MSG,
    ),
    ot_flash_binary = ":rom_ext_virt_a_owner_virt_a",
    signed = True,
    targets = ["cw310"],
)
