# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST", "hex")
load("//rules:linker.bzl", "ld_library")
load("//rules:manifest.bzl", "manifest")
load(
    "//rules:opentitan.bzl",
    "RSA_ONLY_KEY_STRUCTS",
    "RSA_ONLY_ROM_EXT_KEY_STRUCTS",
    "opentitan_flash_binary",
    "opentitan_multislot_flash_binary",
)
load("//rules:opentitan_test.bzl", "cw310_params", "opentitan_functest")
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_alert_classification",
    "otp_alert_digest",
    "otp_bytestring",
    "otp_hex",
    "otp_image",
    "otp_json",
    "otp_partition",
    "otp_per_class_bytes",
    "otp_per_class_ints",
    "otp_per_class_lists",
)
load("//rules:splice.bzl", "bitstream_splice")

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
        "//sw/device/silicon_creator/lib:manifest_def",
        "//sw/device/silicon_creator/lib:rom_print",
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

opentitan_flash_binary(
    name = "bare_metal_slot_a",
    srcs = ["bare_metal_start.S"],
    manifest = ":manifest_standard",
    signed = True,
    deps = [
        ":bare_metal",
        ":ld_slot_a",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

opentitan_flash_binary(
    name = "bare_metal_slot_b",
    srcs = ["bare_metal_start.S"],
    manifest = ":manifest_standard",
    signed = True,
    deps = [
        ":bare_metal",
        ":ld_slot_b",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

opentitan_flash_binary(
    name = "bare_metal_slot_virtual",
    srcs = ["bare_metal_start.S"],
    manifest = ":manifest_virtual",
    signed = True,
    deps = [
        ":bare_metal",
        ":ld_slot_virtual",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

################################################################################
# Bare metal ROM_EXT + BL0 test that DOES NOT use OTTF.
################################################################################
opentitan_multislot_flash_binary(
    name = "rom_ext_virtual_bare_metal_virtual",
    srcs = {
        "//sw/device/silicon_creator/rom_ext:rom_ext_slot_virtual": {
            "key": RSA_ONLY_KEY_STRUCTS[0],
            "offset": "0x0",
        },
        ":bare_metal_slot_virtual": {
            "key": RSA_ONLY_ROM_EXT_KEY_STRUCTS[0],
            "offset": "0x10000",
        },
    },
)

otp_json(
    name = "otp_json_secret2_locked",
    partitions = [
        otp_partition(
            name = "SECRET2",
            items = {
                "CREATOR_ROOT_KEY_SHARE0": "<random>",
                "CREATOR_ROOT_KEY_SHARE1": "<random>",
            },
            lock = True,
        ),
    ],
    visibility = ["//visibility:private"],
)

otp_image(
    name = "otp_img_secret2_locked_rma",
    src = "//hw/ip/otp_ctrl/data:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [
        ":otp_json_secret2_locked",
    ],
    visibility = ["//visibility:private"],
)

bitstream_splice(
    name = "bitstream_secret2_locked",
    src = "//hw/bitstream:rom_with_fake_keys",
    data = ":otp_img_secret2_locked_rma",
    meminfo = "//hw/bitstream:otp_mmi",
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

BOOT_SUCCESS_MSG = "Bare metal PASS!"

opentitan_functest(
    name = "rom_ext_virtual_bare_metal_virtual_boot_test",
    cw310 = cw310_params(
        bitstream = ":bitstream_secret2_locked",
        exit_success = BOOT_SUCCESS_MSG,
    ),
    key_struct = "multislot",
    ot_flash_binary = ":rom_ext_virtual_bare_metal_virtual",
    signed = True,
    targets = ["cw310_rom_with_fake_keys"],
)

################################################################################
# Bare metal ROM_EXT + BL0 test that DOES use OTTF.
################################################################################
opentitan_flash_binary(
    name = "ottf_test_bl0_slot_virtual",
    srcs = ["empty_test.c"],
    manifest = "//sw/device/silicon_owner/bare_metal:manifest_virtual",
    signed = True,
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_multislot_flash_binary(
    name = "rom_ext_virtual_ottf_bl0_virtual",
    srcs = {
        "//sw/device/silicon_creator/rom_ext:rom_ext_slot_virtual": {
            "key": RSA_ONLY_KEY_STRUCTS[0],
            "offset": "0x0",
        },
        ":ottf_test_bl0_slot_virtual": {
            "key": RSA_ONLY_ROM_EXT_KEY_STRUCTS[0],
            "offset": "0x10000",
        },
    },
)

opentitan_functest(
    name = "rom_ext_virtual_ottf_bl0_virtual_test",
    cw310 = cw310_params(
        bitstream = ":bitstream_secret2_locked",
    ),
    key_struct = "multislot",
    ot_flash_binary = ":rom_ext_virtual_ottf_bl0_virtual",
    signed = True,
    targets = ["cw310_rom_with_fake_keys"],
)
