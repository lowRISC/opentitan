# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@lowrisc_opentitan//rules/opentitan:transform.bzl", "obj_transform")
load("//rules/coverage:asm.bzl", "asm_library_with_coverage")
load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU", "opentitan_binary")
load("//rules:linker.bzl", "ld_library")
load(
    "//sw/device/silicon_creator/rom_ext/imm_section:defs.bzl",
    "DEFAULT_EXEC_ENV",
    "IMM_SECTION_MAJOR_VERSION",
    "IMM_SECTION_MINOR_VERSION",
)
load(
    "//sw/device/silicon_creator/rom_ext:defs.bzl",
    "ROM_EXT_VARIATIONS",
    "SLOTS",
)
load(
    "//sw/device/silicon_creator/rom_ext/imm_section:utils.bzl",
    "create_imm_section_targets",
    "imm_section_bundle",
)
load("//util/design:hardened.bzl", "hardened_comparison_test")

package(default_visibility = ["//visibility:public"])

asm_library_with_coverage(
    name = "imm_section_start",
    srcs = ["imm_section_start.S"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/coverage:api_asm",
    ],
)

cc_library(
    name = "main_lib",
    srcs = ["imm_section.c"],
    hdrs = ["imm_section.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":imm_section_epmp",
        ":imm_section_start",
        ":imm_section_version_def",
        "//hw/top_earlgrey/ip_autogen/flash_ctrl:flash_ctrl_c_regs",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/coverage:api",
        "//sw/device/lib/coverage:api_asm",
        "//sw/device/lib/coverage:uart_runtime",
        "//sw/device/silicon_creator/lib:epmp_state",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:manifest",
        "//sw/device/silicon_creator/lib/base:boot_measurements",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/base:static_critical",
        "//sw/device/silicon_creator/lib/base:static_dice",
        "//sw/device/silicon_creator/lib/cert:dice_chain",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:otbn",
        "//sw/device/silicon_creator/lib/drivers:rnd",
        "//sw/device/silicon_creator/lib/ownership:ownership_key",
        "//sw/device/silicon_creator/rom_ext:rom_ext_manifest",
    ],
)

cc_library(
    name = "imm_section_version",
    hdrs = ["imm_section_version.h"],
    deps = [
        "//sw/device/lib/base:macros",
    ],
)

cc_library(
    name = "imm_section_version_def",
    srcs = [
        "imm_section_version_def.c",
        "//rules:autogen_stamp_include",
    ],
    local_defines = [
        "IMM_SECTION_MAJOR_VERSION={}".format(IMM_SECTION_MAJOR_VERSION),
        "IMM_SECTION_MINOR_VERSION={}".format(IMM_SECTION_MINOR_VERSION),
    ],
    deps = [
        ":imm_section_version",
    ],
    alwayslink = True,
)

cc_library(
    name = "imm_section_epmp",
    srcs = ["imm_section_epmp.c"],
    hdrs = ["imm_section_epmp.h"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:epmp_state",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:manifest",
        "//sw/device/silicon_creator/lib/drivers:epmp",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
    ],
)

ld_library(
    name = "ld_common",
    includes = ["imm_section_common.ld"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
        "//sw/device:info_sections",
        "//sw/device/lib/coverage:coverage_sections",
        "//sw/device/silicon_creator/lib/base:static_critical_sections",
        "//sw/device/silicon_creator/lib/base:static_dice_sections",
    ],
)

[
    ld_library(
        name = "ld_slot_{}".format(slot),
        script = "imm_section_slot_{}.ld".format(slot),
        deps = [
            ":ld_common",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
        ],
    )
    for slot in SLOTS
]

[
    opentitan_binary(
        name = "main_binaries_{}_slot_{}".format(variation_name, slot),
        exec_env = DEFAULT_EXEC_ENV,
        extra_bazel_features = [
            "minsize",
            "use_lld",
        ],
        linker_script = ":ld_slot_{}".format(slot),
        manifest = "//hw/top_earlgrey:none_manifest",
        deps = [
            ":main_lib",
            "//sw/device/lib/crt",
        ] + variation_deps,
    )
    for variation_name, variation_deps in ROM_EXT_VARIATIONS.items()
    for slot in SLOTS
]

[
    hardened_comparison_test(
        name = "main_binaries_{}_slot_{}_hardened_comparison_test".format(variation_name, slot),
        srcs = [":main_binaries_{}_slot_{}".format(variation_name, slot)],
    )
    for variation_name, variation_deps in ROM_EXT_VARIATIONS.items()
    for slot in SLOTS
]

[
    create_imm_section_targets(
        name = "main_section_{}_slot_{}".format(variation_name, slot),
        src = ":main_binaries_{}_slot_{}".format(variation_name, slot),
    )
    for variation_name, variation_deps in ROM_EXT_VARIATIONS.items()
    for slot in SLOTS
]

imm_section_bundle(
    name = "release_bundle",
    variants = {
        variation_name: ":main_binaries_{}_slot_virtual".format(variation_name)
        for variation_name, _ in ROM_EXT_VARIATIONS.items()
    },
)
