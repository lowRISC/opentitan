# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@lowrisc_opentitan//rules/opentitan:transform.bzl", "obj_transform")
load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU", "opentitan_binary")
load("//rules:linker.bzl", "ld_library")
load("//sw/device/silicon_creator/rom_ext/imm_section:defs.bzl", "DEFAULT_EXEC_ENV")
load(
    "//sw/device/silicon_creator/rom_ext/imm_section:utils.bzl",
    "create_imm_section_targets",
)

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "main_lib",
    srcs = [
        "imm_section.c",
        "imm_section_start.S",
    ],
    hdrs = ["imm_section.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":imm_section_epmp",
        "//hw/top:flash_ctrl_c_regs",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:epmp_state",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:manifest",
        "//sw/device/silicon_creator/lib/base:boot_measurements",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/base:static_critical",
        "//sw/device/silicon_creator/lib/base:static_dice",
        "//sw/device/silicon_creator/lib/cert:dice_chain",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/drivers:rnd",
        "//sw/device/silicon_creator/lib/ownership:ownership_key",
        "//sw/device/silicon_creator/rom_ext:rom_ext_manifest",
    ],
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
        "//sw/device/silicon_creator/lib/base:static_critical_sections",
        "//sw/device/silicon_creator/lib/base:static_dice_sections",
    ],
)

ld_library(
    name = "ld_slot_a",
    script = "imm_section_slot_a.ld",
    deps = [
        ":ld_common",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
    ],
)

ld_library(
    name = "ld_slot_b",
    script = "imm_section_slot_b.ld",
    deps = [
        ":ld_common",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
    ],
)

ld_library(
    name = "ld_slot_virtual",
    script = "imm_section_slot_virtual.ld",
    deps = [
        ":ld_common",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
    ],
)

opentitan_binary(
    name = "main_binaries_slot_a",
    exec_env = DEFAULT_EXEC_ENV,
    linker_script = ":ld_slot_a",
    manifest = "//hw/top_earlgrey:none_manifest",
    transitive_features = [
        "minsize",
        "use_lld",
    ],
    deps = [
        ":main_lib",
        "//sw/device/lib/crt",
    ],
)

create_imm_section_targets(
    name = "main_section_slot_a",
    src = ":main_binaries_slot_a",
)

opentitan_binary(
    name = "main_binaries_slot_b",
    exec_env = DEFAULT_EXEC_ENV,
    linker_script = ":ld_slot_b",
    manifest = "//hw/top_earlgrey:none_manifest",
    transitive_features = [
        "minsize",
        "use_lld",
    ],
    deps = [
        ":main_lib",
        "//sw/device/lib/crt",
    ],
)

create_imm_section_targets(
    name = "main_section_slot_b",
    src = ":main_binaries_slot_b",
)

opentitan_binary(
    name = "main_binaries_slot_virtual",
    exec_env = DEFAULT_EXEC_ENV,
    linker_script = ":ld_slot_virtual",
    manifest = "//hw/top_earlgrey:none_manifest",
    transitive_features = [
        "minsize",
        "use_lld",
    ],
    deps = [
        ":main_lib",
        "//sw/device/lib/crt",
    ],
)

create_imm_section_targets(
    name = "main_section_slot_virtual",
    src = ":main_binaries_slot_virtual",
)
