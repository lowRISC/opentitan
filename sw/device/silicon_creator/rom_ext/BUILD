# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST", "hex")
load("//rules:cross_platform.bzl", "dual_cc_library", "dual_inputs")
load("//rules:linker.bzl", "ld_library")
load("//rules:manifest.bzl", "manifest")
load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU", "opentitan_binary")
load(
    "//sw/device/silicon_creator/rom_ext:defs.bzl",
    "ROM_EXT_VARIATIONS",
    "ROM_EXT_VERSION",
    "SLOTS",
)

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "doc_files",
    srcs = glob(["**/*.md"]),
)

cc_library(
    name = "rom_ext_manifest",
    srcs = ["rom_ext_manifest.c"],
    hdrs = ["rom_ext_manifest.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:manifest",
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
    name = "rom_ext_isrs",
    srcs = [
        "rom_ext_isrs.c",
        "//sw/device/silicon_creator/lib:flash_exc_handler",
    ],
    hdrs = ["rom_ext_isrs.h"],
    defines = [
        "INTERRUPT_HANDLER=rom_ext_interrupt_handler",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top:flash_ctrl_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:dbg_print",
        "//sw/device/silicon_creator/lib:error",
    ],
)

ld_library(
    name = "ld_common",
    includes = ["rom_ext_common.ld"],
    deps = [
        "//sw/device:info_sections",
        "//sw/device/silicon_creator/lib/base:static_critical_sections",
        "//sw/device/silicon_creator/lib/base:static_dice_sections",
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

[
    cc_library(
        name = "rom_ext_{}".format(variation_name),
        srcs = [
            "rom_ext.c",
            "rom_ext_start.S",
        ],
        hdrs = ["rom_ext.h"],
        target_compatible_with = [OPENTITAN_CPU],
        deps = [
            ":rom_ext_boot_policy",
            ":rom_ext_boot_policy_ptrs",
            ":rom_ext_isrs",
            ":rom_ext_manifest",
            "//hw/top:flash_ctrl_c_regs",
            "//hw/top:sram_ctrl_c_regs",
            "//hw/top/dt",
            "//sw/device/lib/arch:device",
            "//sw/device/lib/base:csr",
            "//sw/device/lib/base:macros",
            "//sw/device/lib/base:memory",
            "//sw/device/lib/base:stdasm",
            "//sw/device/lib/runtime:hart",
            "//sw/device/silicon_creator/lib:boot_data",
            "//sw/device/silicon_creator/lib:boot_log",
            "//sw/device/silicon_creator/lib:dbg_print",
            "//sw/device/silicon_creator/lib:epmp_state",
            "//sw/device/silicon_creator/lib:manifest",
            "//sw/device/silicon_creator/lib:manifest_def",
            "//sw/device/silicon_creator/lib:shutdown",
            "//sw/device/silicon_creator/lib/base:boot_measurements",
            "//sw/device/silicon_creator/lib/base:chip",
            "//sw/device/silicon_creator/lib/base:sec_mmio",
            "//sw/device/silicon_creator/lib/base:static_critical",
            "//sw/device/silicon_creator/lib/base:static_dice",
            "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
            "//sw/device/silicon_creator/lib/cert:dice_chain",
            "//sw/device/silicon_creator/lib/drivers:ast",
            "//sw/device/silicon_creator/lib/drivers:epmp",
            "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
            "//sw/device/silicon_creator/lib/drivers:hmac",
            "//sw/device/silicon_creator/lib/drivers:ibex",
            "//sw/device/silicon_creator/lib/drivers:lifecycle",
            "//sw/device/silicon_creator/lib/drivers:otp",
            "//sw/device/silicon_creator/lib/drivers:pinmux",
            "//sw/device/silicon_creator/lib/drivers:retention_sram",
            "//sw/device/silicon_creator/lib/drivers:rnd",
            "//sw/device/silicon_creator/lib/drivers:uart",
            "//sw/device/silicon_creator/lib/ownership",
            "//sw/device/silicon_creator/lib/ownership:owner_verify",
            "//sw/device/silicon_creator/lib/ownership:ownership_activate",
            "//sw/device/silicon_creator/lib/ownership:ownership_unlock",
            "//sw/device/silicon_creator/lib/rescue:rescue_xmodem",
            "//sw/device/silicon_creator/lib/sigverify",
            "//sw/device/silicon_creator/rom_ext/imm_section:imm_section_version",
            "//sw/otbn/crypto:boot",
        ] + variation_deps,
    )
    for variation_name, variation_deps in ROM_EXT_VARIATIONS.items()
]

manifest(d = {
    "name": "manifest",
    "identifier": hex(CONST.ROM_EXT),
    "visibility": ["//visibility:public"],
    "version_major": ROM_EXT_VERSION.MAJOR,
    "version_minor": ROM_EXT_VERSION.MINOR,
    "security_version": ROM_EXT_VERSION.SECURITY,
})

ROM_EXT_FEATURES = [
    "minsize",
    "use_lld",
]

[
    opentitan_binary(
        name = "rom_ext_{}_slot_{}".format(variation_name, slot),
        testonly = True,
        collect_code_coverage = 0,
        # TODO(#22780): Integrate real keys for A1 flows.
        ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
        exec_env = [
            "//hw/top_earlgrey:fpga_cw310",
            "//hw/top_earlgrey:fpga_cw340",
            "//hw/top_earlgrey:sim_dv_base",
            "//hw/top_earlgrey:sim_verilator_base",
            "//hw/top_earlgrey:silicon_creator",
        ],
        linker_script = ":ld_slot_{}".format(slot),
        manifest = ":manifest",
        spx_key = {"//sw/device/silicon_creator/rom/keys/fake/spx:prod_key_0_spx": "prod_key_0"},
        transitive_features = ROM_EXT_FEATURES,
        deps = [
            ":rom_ext_{}".format(variation_name),
            "//sw/device/lib/crt",
            "//sw/device/silicon_creator/lib:manifest_def",
            "//sw/device/silicon_creator/lib/ownership:test_owner",
            "//sw/device/silicon_creator/lib/ownership/keys/fake",
            "//sw/device/silicon_creator/rom_ext/imm_section:main_section_{}_slot_{}".format(variation_name, slot),
        ],
    )
    for variation_name, variation_deps in ROM_EXT_VARIATIONS.items()
    for slot in SLOTS
]

# This binary is a test-only ROM_EXT that has ownership initialized in
# the "NewVersion" update mode.  Initializing in this mode makes the
# test flows for the "NewVersion" style of ownership updates easier.
opentitan_binary(
    name = "rom_ext_owner_update_newversion",
    testonly = True,
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310",
        "//hw/top_earlgrey:fpga_cw340",
    ],
    linker_script = ":ld_slot_a",
    manifest = ":manifest",
    deps = [
        ":rom_ext_dice_x509",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
        "//sw/device/silicon_creator/lib/ownership:test_owner_update_mode_newversion",
        "//sw/device/silicon_creator/lib/ownership/keys/fake",
        "//sw/device/silicon_creator/rom_ext/imm_section:main_section_dice_x509_slot_a",
    ],
)

opentitan_binary(
    name = "rom_ext_hybrid_owner_keys",
    testonly = True,
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310",
        "//hw/top_earlgrey:fpga_cw340",
    ],
    linker_script = ":ld_slot_a",
    manifest = ":manifest",
    transitive_features = ROM_EXT_FEATURES,
    deps = [
        ":rom_ext_dice_x509",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
        "//sw/device/silicon_creator/lib/ownership:test_owner_hybrid",
        "//sw/device/silicon_creator/lib/ownership/keys/fake",
        "//sw/device/silicon_creator/rom_ext/imm_section:main_section_dice_x509_slot_a",
    ],
)

manifest(d = {
    "name": "manifest_bad_address_translation",
    "address_translation": "0",
    "identifier": hex(CONST.ROM_EXT),
})

opentitan_binary(
    name = "rom_ext_dice_x509_slot_a_bad_address_translation",
    testonly = True,
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:test_key_0_ecdsa_p256": "test_key_0"},
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310",
        "//hw/top_earlgrey:fpga_cw340",
        "//hw/top_earlgrey:sim_dv_base",
        "//hw/top_earlgrey:sim_verilator_base",
    ],
    linker_script = ":ld_slot_a",
    manifest = ":manifest_bad_address_translation",
    transitive_features = ROM_EXT_FEATURES,
    deps = [
        ":rom_ext_dice_x509",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
        "//sw/device/silicon_creator/lib/ownership:test_owner",
        "//sw/device/silicon_creator/lib/ownership/keys/fake",
    ],
)
