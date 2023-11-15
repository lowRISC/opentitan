# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST", "hex")
load("//rules:linker.bzl", "ld_library")
load("//rules:manifest.bzl", "manifest")
load("//rules/opentitan:defs.bzl", "cw310_params", "opentitan_binary", "opentitan_test")

package(default_visibility = ["//visibility:public"])

ld_library(
    name = "ld_common",
    includes = ["bare_metal_common.ld"],
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
    name = "ld_slot_virtual",
    script = "bare_metal_slot_virtual.ld",
    deps = [
        ":ld_common",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
    ],
)

cc_library(
    name = "bare_metal",
    srcs = ["bare_metal.c"],
    hdrs = ["bare_metal.h"],
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:dbg_print",
        "//sw/device/silicon_creator/lib:manifest_def",
        "//sw/device/silicon_creator/lib/base:static_critical",
    ],
)

manifest({
    "name": "manifest_standard",
    "address_translation": hex(CONST.HARDENED_FALSE),
    "identifier": hex(CONST.OWNER),
})

manifest({
    "name": "manifest_virtual",
    "address_translation": hex(CONST.HARDENED_TRUE),
    "identifier": hex(CONST.OWNER),
})

opentitan_binary(
    name = "bare_metal_slot_a",
    testonly = True,
    srcs = ["bare_metal_start.S"],
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310_rom_ext",
    ],
    linker_script = ":ld_slot_a",
    manifest = ":manifest_standard",
    deps = [
        ":bare_metal",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

opentitan_binary(
    name = "bare_metal_slot_b",
    testonly = True,
    srcs = ["bare_metal_start.S"],
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310_rom_ext",
    ],
    linker_script = ":ld_slot_b",
    manifest = ":manifest_standard",
    deps = [
        ":bare_metal",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

opentitan_binary(
    name = "bare_metal_slot_virtual",
    testonly = True,
    srcs = ["bare_metal_start.S"],
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310_rom_ext",
    ],
    linker_script = ":ld_slot_virtual",
    manifest = ":manifest_virtual",
    deps = [
        ":bare_metal",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

################################################################################
# Bare metal ROM_EXT + BL0 test that DOES NOT use OTTF.
# - This test uses stand-alone binaries emitted by the opentitan_binary rule.
# - The test assembles an image containing the ROM_EXT from the exec_env and
#   the binary specified in the cw310 parameters.
################################################################################
BOOT_SUCCESS_MSG = "Bare metal PASS!"

opentitan_test(
    name = "rom_ext_virtual_bare_metal_virtual_boot_test",
    cw310 = cw310_params(
        binaries = {
            ":bare_metal_slot_virtual": "firmware",
        },
        exit_success = BOOT_SUCCESS_MSG,
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
    },
)

################################################################################
# Bare metal ROM_EXT + BL0 test that DOES use OTTF.
# - This test build a test program in the test rule and then assembles an image
#   containing the ROM_EXT from the exec_env an the compiled test program.
################################################################################
opentitan_test(
    name = "rom_ext_virtual_ottf_bl0_virtual",
    srcs = ["empty_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
    },
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    manifest = ":manifest_virtual",
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
