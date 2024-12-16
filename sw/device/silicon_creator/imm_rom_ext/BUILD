# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@lowrisc_opentitan//rules/opentitan:exec_env.bzl", "ExecEnvInfo")
load("@lowrisc_opentitan//rules/opentitan:transform.bzl", "obj_transform")
load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU", "opentitan_binary")
load("//rules:linker.bzl", "ld_library")
load("//sw/device/silicon_creator/imm_rom_ext:defs.bzl", "DEFAULT_EXEC_ENV")
load(
    "//sw/device/silicon_creator/imm_rom_ext:utils.bzl",
    "create_imm_rom_ext_targets",
)

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "main_lib",
    srcs = [
        "hello_world_start.S",
        "imm_rom_ext.c",
    ],
    hdrs = ["imm_rom_ext.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":imm_rom_ext_epmp",
        "//hw/top:flash_ctrl_c_regs",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:dbg_print",
        "//sw/device/silicon_creator/lib:epmp_state",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:manifest",
        "//sw/device/silicon_creator/lib:shutdown",
        "//sw/device/silicon_creator/lib/base:boot_measurements",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/base:static_critical",
        "//sw/device/silicon_creator/lib/cert:dice_chain",
        "//sw/device/silicon_creator/lib/drivers:pinmux",
        "//sw/device/silicon_creator/lib/drivers:rnd",
        "//sw/device/silicon_creator/lib/drivers:uart",
        "//sw/device/silicon_creator/lib/ownership:ownership_key",
        "//sw/device/silicon_creator/rom_ext:rom_ext_manifest",
    ],
)

cc_library(
    name = "imm_rom_ext_epmp",
    srcs = ["imm_rom_ext_epmp.c"],
    hdrs = ["imm_rom_ext_epmp.h"],
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

opentitan_binary(
    name = "main_binaries",
    exec_env = DEFAULT_EXEC_ENV,
    extra_bazel_features = [
        "minsize",
        "use_lld",
    ],
    linker_script = ":ld_hello_world",
    manifest = "//hw/top_earlgrey:none_manifest",
    deps = [
        ":main_lib",
        "//sw/device/lib/crt",
    ],
)

[
    create_imm_rom_ext_targets(
        src = ":main_binaries",
        base_name = "main_section",
        exec_env = env,
    )
    for env in DEFAULT_EXEC_ENV
]

ld_library(
    name = "ld_hello_world",
    script = "hello_world.ld",
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
        "//sw/device:info_sections",
        "//sw/device/silicon_creator/lib/base:static_critical_sections",
    ],
)

cc_library(
    name = "hello_world",
    srcs = [
        "hello_world.c",
        "hello_world_start.S",
    ],
    hdrs = ["hello_world.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/silicon_creator/lib/base:static_critical",
        "//sw/device/silicon_creator/lib/drivers:uart",
    ],
)

opentitan_binary(
    name = "hello_world_binaries",
    exec_env = [
        "//hw/top_earlgrey:fpga_cw340",
    ],
    linker_script = ":ld_hello_world",
    deps = [
        ":hello_world",
        "//sw/device/lib/crt",
    ],
)
