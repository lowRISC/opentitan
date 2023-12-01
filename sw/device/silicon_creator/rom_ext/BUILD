# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST", "hex")
load("//rules:manifest.bzl", "manifest")
load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU", "opentitan_binary")
load("//rules:linker.bzl", "ld_library")
load("//rules:cross_platform.bzl", "dual_cc_library", "dual_inputs")
load("@rules_fuzzing//fuzzing:cc_defs.bzl", "cc_fuzz_test")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "rom_ext_epmp",
    srcs = ["rom_ext_epmp.c"],
    hdrs = ["rom_ext_epmp.h"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:csr",
        "//sw/device/silicon_creator/lib:epmp_state",
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
        "//sw/device/silicon_creator/lib:boot_data",
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

cc_library(
    name = "bootstrap",
    srcs = ["bootstrap.c"],
    hdrs = ["bootstrap.h"],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:bootstrap",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/base:chip",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)

cc_test(
    name = "bootstrap_unittest",
    srcs = ["bootstrap_unittest.cc"],
    deps = [
        ":bootstrap",
        "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//sw/device/lib/base:memory",
        "//sw/device/silicon_creator/lib:bootstrap",
        "//sw/device/silicon_creator/lib:bootstrap_unittest_util",
        "//sw/device/silicon_creator/lib:error_unittest_util",
        "//sw/device/silicon_creator/lib/base:chip",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
        "//sw/device/silicon_creator/lib/drivers:spi_device",
        "//sw/device/silicon_creator/testing:rom_test",
        "@com_google_absl//absl/types:optional",
        "@com_google_absl//absl/types:span",
        "@googletest//:gtest_main",
    ],
)

# To test this target, you must specify `--config=asan-libfuzzer`.
cc_fuzz_test(
    name = "bootstrap_fuzz_test",
    srcs = ["bootstrap_fuzz_test.cc"],
    tags = [
        "fuzzer",
        "manual",
    ],
    deps = [
        ":bootstrap",
        "//sw/device/silicon_creator/lib:bootstrap_fuzzer_util",
        "@com_google_absl//absl/types:span",
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
    name = "sigverify_keys",
    srcs = ["sigverify_keys.c"],
    hdrs = ["sigverify_keys.h"],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/drivers:rnd",
        "//sw/device/silicon_creator/lib/sigverify:rsa_key",
    ],
)

cc_test(
    name = "sigverify_keys_unittest",
    srcs = ["sigverify_keys_unittest.cc"],
    deps = [
        ":sigverify_keys",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "rom_ext",
    srcs = [
        "rom_ext.c",
        "rom_ext_start.S",
    ],
    hdrs = ["rom_ext.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":bootstrap",
        ":rom_ext_boot_policy",
        ":rom_ext_boot_policy_ptrs",
        ":rom_ext_epmp",
        ":sigverify_keys",
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:stdasm",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/runtime:hart",
        "//sw/device/silicon_creator/lib:attestation",
        "//sw/device/silicon_creator/lib:attestation_key_diversifiers",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib:dbg_print",
        "//sw/device/silicon_creator/lib:manifest",
        "//sw/device/silicon_creator/lib:manifest_def",
        "//sw/device/silicon_creator/lib:otbn_boot_services",
        "//sw/device/silicon_creator/lib:shutdown",
        "//sw/device/silicon_creator/lib/base:chip",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/base:static_critical",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:ibex",
        "//sw/device/silicon_creator/lib/drivers:keymgr",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/drivers:pinmux",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rnd",
        "//sw/device/silicon_creator/lib/drivers:uart",
        "//sw/device/silicon_creator/lib/sigverify",
        "//sw/device/silicon_creator/rom_ext/keys/fake",
        "//sw/otbn/crypto:boot",
    ],
)

manifest({
    "name": "manifest_standard",
    "address_translation": hex(CONST.HARDENED_FALSE),
    "identifier": hex(CONST.ROM_EXT),
    "visibility": ["//visibility:public"],
})

manifest({
    "name": "manifest_virtual",
    "address_translation": hex(CONST.HARDENED_TRUE),
    "identifier": hex(CONST.ROM_EXT),
})

opentitan_binary(
    name = "rom_ext_slot_a",
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310",
        "//hw/top_earlgrey:sim_dv_base",
        "//hw/top_earlgrey:sim_verilator_base",
    ],
    linker_script = ":ld_slot_a",
    manifest = ":manifest_standard",
    rsa_key = {"//sw/device/silicon_creator/rom/keys/fake/rsa:test_private_key_0": "test_key_0"},
    deps = [
        ":rom_ext",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

opentitan_binary(
    name = "rom_ext_slot_b",
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310",
        "//hw/top_earlgrey:sim_dv_base",
        "//hw/top_earlgrey:sim_verilator_base",
    ],
    linker_script = ":ld_slot_b",
    manifest = ":manifest_standard",
    rsa_key = {"//sw/device/silicon_creator/rom/keys/fake/rsa:test_private_key_0": "test_key_0"},
    deps = [
        ":rom_ext",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

opentitan_binary(
    name = "rom_ext_slot_virtual",
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310",
        "//hw/top_earlgrey:sim_dv_base",
        "//hw/top_earlgrey:sim_verilator_base",
    ],
    linker_script = ":ld_slot_virtual",
    manifest = ":manifest_virtual",
    rsa_key = {"//sw/device/silicon_creator/rom/keys/fake/rsa:test_private_key_0": "test_key_0"},
    deps = [
        ":rom_ext",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

manifest({
    "name": "manifest_bad_address_translation",
    "address_translation": "0",
    "identifier": hex(CONST.ROM_EXT),
})

opentitan_binary(
    name = "rom_ext_slot_a_bad_address_translation",
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310",
        "//hw/top_earlgrey:sim_dv_base",
        "//hw/top_earlgrey:sim_verilator_base",
    ],
    linker_script = ":ld_slot_a",
    manifest = ":manifest_bad_address_translation",
    rsa_key = {"//sw/device/silicon_creator/rom/keys/fake/rsa:test_private_key_0": "test_key_0"},
    deps = [
        ":rom_ext",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)
