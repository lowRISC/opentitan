# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@opentitan_signing_infra//toolchains/opentitantool:opentitantool.bzl", "opentitantool")
load("@rules_cc//cc/toolchains:actions.bzl", "cc_action_type")
load("@rules_cc//cc/toolchains:args.bzl", "cc_args")
load("@rules_cc//cc/toolchains:args_list.bzl", "cc_args_list")
load("@rules_cc//cc/toolchains:feature.bzl", "cc_feature")
load("@rules_cc//cc/toolchains:feature_constraint.bzl", "cc_feature_constraint")
load("@rules_cc//cc/toolchains:feature_set.bzl", "cc_feature_set")
load("@rules_cc//cc/toolchains:toolchain.bzl", "cc_toolchain")
load("@rules_cc//cc/toolchains:tool_map.bzl", "cc_tool_map")
load(
    "//rules:actions.bzl",
    "OT_ACTION_LLVM_PROFDATA",
    "OT_ACTION_NM",
    "OT_ACTION_OBJDUMP",
)

package(default_visibility = ["//visibility:public"])

# Toolchain arguments that are independent of the target ISA.
COMMON_TOOLCHAIN_ARGS = [
    ":warnings",
    ":reproducible",
    ":symbol_garbage_collection",
    ":constructor_destructor",
    ":nostdinc",
    ":discard_locals",
]

COMMON_ENABLED_FEATURES = [
    "@rules_cc//cc/toolchains/args:experimental_replace_legacy_action_config_features",
    ":feat_warnings_as_errors",
    ":feat_use_lld",
    ":feat_lto",
    ":feat_minsize",
    ":feat_rv32_bitmanip",
]

COMMON_KNOWN_FEATURES = [
    "@rules_cc//cc/toolchains/args:experimental_replace_legacy_action_config_features",
    ":feat_warnings_as_errors",
    ":feat_guards",
    ":feat_coverage",
    ":feat_use_lld",
    ":feat_lto",
    ":feat_minsize",
    ":feat_dbg",
    ":feat_fastbuild",
    ":feat_opt",
    ":feat_rv32_bitmanip",
    ":feat_no_jump_tables",
]

# OpenTitanTool toolchain for usage in upstream signing rules
opentitantool(
    name = "latest_opentitantool",
    tool = "//sw/host/opentitantool",
)

toolchain(
    name = "latest_opentitantool_toolchain",
    exec_compatible_with = ["@platforms//cpu:x86_64"],
    toolchain = ":latest_opentitantool",
    toolchain_type = "@opentitan_signing_infra//toolchains/opentitantool:toolchain_type",
)

platform(
    name = "opentitan_platform",
    constraint_values = [
        "@platforms//cpu:riscv32",
        "@platforms//os:none",
        ":device",
    ],
)

platform(
    name = "cheriot_platform",
    constraint_values = [
        "@platforms//cpu:riscv32",
        "@platforms//os:none",
        ":device",
        ":isa_cheriot",
    ],
)

# The ISA needs its own constraint setting because `@platforms//cpu` has no
# CHERIoT value.
constraint_setting(
    name = "isa",
    default_constraint_value = ":isa_rv32",
)

constraint_value(
    name = "isa_rv32",
    constraint_setting = ":isa",
)

constraint_value(
    name = "isa_cheriot",
    constraint_setting = ":isa",
)

constraint_setting(name = "target")

constraint_value(
    name = "host",
    constraint_setting = "target",
)

constraint_value(
    name = "device",
    constraint_setting = "target",
)

config_setting(
    name = "on_device_config",
    constraint_values = [":device"],
)

toolchain(
    name = "cc_toolchain_opentitan",
    exec_compatible_with = ["@platforms//cpu:x86_64"],
    target_compatible_with = [
        "@platforms//cpu:riscv32",
        "@platforms//os:none",
        ":isa_rv32",
    ],
    toolchain = ":opentitan_toolchain",
    toolchain_type = "@bazel_tools//tools/cpp:toolchain_type",
)

toolchain(
    name = "cc_toolchain_cheriot",
    exec_compatible_with = ["@platforms//cpu:x86_64"],
    target_compatible_with = [
        "@platforms//cpu:riscv32",
        "@platforms//os:none",
        ":isa_cheriot",
    ],
    toolchain = ":cheriot_toolchain",
    toolchain_type = "@bazel_tools//tools/cpp:toolchain_type",
)

# Collects a set of tools, arguments, and features into a C/C++ toolchain.
cc_toolchain(
    name = "opentitan_toolchain",
    args = [
        ":system_includes",
        ":arch_rv32imc",
        ":arch_rv32imcb",
        ":abi",
        ":disassemble",
    ] + COMMON_TOOLCHAIN_ARGS,
    enabled_features = COMMON_ENABLED_FEATURES,
    known_features = COMMON_KNOWN_FEATURES,
    tool_map = ":tool_map",
)

cc_toolchain(
    name = "cheriot_toolchain",
    args = [
        ":system_includes_cheriot",
        ":arch_cheriot",
        ":arch_cheriot_no_bitmanip",
        ":abi_cheriot",
        ":disassemble_cheriot",
    ] + COMMON_TOOLCHAIN_ARGS,
    # Not yet warning-clean under purecap. Drop this once the C libraries are.
    enabled_features = [
        f
        for f in COMMON_ENABLED_FEATURES
        if f != ":feat_warnings_as_errors"
    ],
    known_features = COMMON_KNOWN_FEATURES,
    tool_map = ":cheriot_tool_map",
)

# Map from C/C++ compilation actions to tools, with `{}` for the toolchain
# archive the binaries come from.
COMMON_TOOLS = {
    "@rules_cc//cc/toolchains/actions:ar_actions": "{}//:ar",
    "@rules_cc//cc/toolchains/actions:assembly_actions": "{}//:clang",
    "@rules_cc//cc/toolchains/actions:c_compile": "{}//:clang",
    "@rules_cc//cc/toolchains/actions:cpp_compile_actions": "{}//:clang++",
    "@rules_cc//cc/toolchains/actions:link_actions": "{}//:clang",
    "@rules_cc//cc/toolchains/actions:llvm_cov": "{}//:llvm_cov",
    "@rules_cc//cc/toolchains/actions:objcopy_embed_data": "{}//:objcopy",
    "@rules_cc//cc/toolchains/actions:strip": "{}//:strip",
    ":action_llvm_profdata": "{}//:llvm_profdata",
    ":action_nm": "{}//:nm",
}

cc_tool_map(
    name = "tool_map",
    tools = {
        k: v.format("@lowrisc_rv32imcb_toolchain")
        for k, v in COMMON_TOOLS.items()
    } | {
        ":action_objdump": "@lowrisc_rv32imcb_toolchain//:objdump",
    },
)

# Identical to `:tool_map`, except that disassembly goes through `llvm-objdump`,
# which can decode CHERI instructions.
cc_tool_map(
    name = "cheriot_tool_map",
    tools = {
        k: v.format("@lowrisc_cheriot_toolchain")
        for k, v in COMMON_TOOLS.items()
    } | {
        ":action_objdump": "@lowrisc_cheriot_toolchain//:llvm_objdump",
    },
)

cc_action_type(
    name = "action_llvm_profdata",
    action_name = OT_ACTION_LLVM_PROFDATA,
)

cc_action_type(
    name = "action_nm",
    action_name = OT_ACTION_NM,
)

cc_action_type(
    name = "action_objdump",
    action_name = OT_ACTION_OBJDUMP,
)

DISASSEMBLE_ARGS = [
    "-wx",
    "--disassemble",
    "--line-numbers",
    "--disassemble-zeroes",
    "--source",
]

cc_args(
    name = "disassemble",
    actions = [":action_objdump"],
    args = DISASSEMBLE_ARGS + ["--visualize-jumps"],
)

# `llvm-objdump` does not accept `--visualize-jumps`.
cc_args(
    name = "disassemble_cheriot",
    actions = [":action_objdump"],
    args = DISASSEMBLE_ARGS,
)

# minsize feature to switch between Os and Oz.
cc_feature(
    name = "feat_minsize",
    feature_name = "minsize",
)

cc_feature_constraint(
    name = "constraint_minsize",
    all_of = [":feat_minsize"],
)

cc_feature_constraint(
    name = "constraint_no_minsize",
    none_of = [":feat_minsize"],
)

cc_feature_constraint(
    name = "constraint_minsize_lld",
    all_of = [
        ":feat_minsize",
        ":feat_use_lld",
    ],
)

# Built-in Bazel feature enabled for optimized builds.
cc_feature(
    name = "feat_opt",
    args = [
        ":optsize",
        ":minsize",
        ":minsize_inline_cc",
        ":minsize_inline_ld",
        ":default_debug_info",
        ":lto",
    ],
    overrides = "@rules_cc//cc/toolchains/features:opt",
)

cc_args(
    name = "default_debug_info",
    actions = ["@rules_cc//cc/toolchains/actions:compile_actions"],
    args = [
        "-g",
        "-gdwarf-4",
    ],
)

cc_args(
    name = "optsize",
    actions = ["@rules_cc//cc/toolchains/actions:compile_actions"],
    args = [
        "-Os",
    ],
    requires_any_of = [":constraint_no_minsize"],
)

cc_args(
    name = "minsize",
    actions = ["@rules_cc//cc/toolchains/actions:compile_actions"],
    args = [
        "-Oz",
    ],
    requires_any_of = [":constraint_minsize"],
)

# Inline slightly more which is actually smaller.
cc_args(
    name = "minsize_inline_cc",
    actions = ["@rules_cc//cc/toolchains/actions:compile_actions"],
    args = [
        "-mllvm",
        "--inline-threshold=10",
    ],
    requires_any_of = [":constraint_minsize_lld"],
)

cc_args(
    name = "minsize_inline_ld",
    actions = ["@rules_cc//cc/toolchains/actions:link_actions"],
    args = [
        "-Wl,-mllvm",
        "-Wl,--inline-threshold=10",
    ],
    requires_any_of = [":constraint_minsize_lld"],
)

# Built-in Bazel feature enabled for debug builds.
cc_feature(
    name = "feat_dbg",
    args = [":dbg"],
    overrides = "@rules_cc//cc/toolchains/features:dbg",
)

cc_args(
    name = "dbg",
    actions = ["@rules_cc//cc/toolchains/actions:compile_actions"],
    args = [
        "-O0",
        "-g3",
    ],
)

# Built-in Bazel feature for fast builds.
cc_feature(
    name = "feat_fastbuild",
    args = [
        ":optsize",
        ":minsize",
        ":minsize_inline_cc",
        ":minsize_inline_ld",
        ":default_debug_info",
    ],
    overrides = "@rules_cc//cc/toolchains/features:fastbuild",
)

cc_args(
    name = "nostdinc",
    actions = ["@rules_cc//cc/toolchains/actions:compile_actions"],
    args = ["-nostdinc"],
)

cc_args(
    name = "system_includes",
    actions = ["@rules_cc//cc/toolchains/actions:compile_actions"],
    args = [
        "-isystem",
        "{clang-include}",
        "-isystem",
        "{freestanding}",
    ],
    data = [
        "//sw/device/lib/base/freestanding",
        "@lowrisc_rv32imcb_toolchain//:lib-clang-include",
    ],
    format = {
        "clang-include": "@lowrisc_rv32imcb_toolchain//:lib-clang-include",
        "freestanding": "//sw/device/lib/base/freestanding",
    },
)

# The same, but resolved against the CHERIoT toolchain's clang.
cc_args(
    name = "system_includes_cheriot",
    actions = ["@rules_cc//cc/toolchains/actions:compile_actions"],
    args = [
        "-isystem",
        "{clang-include}",
        "-isystem",
        "{freestanding}",
    ],
    data = [
        "//sw/device/lib/base/freestanding",
        "@lowrisc_cheriot_toolchain//:lib-clang-include",
    ],
    format = {
        "clang-include": "@lowrisc_cheriot_toolchain//:lib-clang-include",
        "freestanding": "//sw/device/lib/base/freestanding",
    },
)

# This feature can be disabled to remove the bitmanip extensions.
cc_feature(
    name = "feat_rv32_bitmanip",
    feature_name = "rv32_bitmanip",
)

cc_feature_constraint(
    name = "constraint_bitmanip",
    all_of = [":feat_rv32_bitmanip"],
)

cc_feature_constraint(
    name = "constraint_no_bitmanip",
    none_of = [":feat_rv32_bitmanip"],
)

cc_args(
    name = "arch_rv32imcb",
    actions = [
        "@rules_cc//cc/toolchains/actions:compile_actions",
        "@rules_cc//cc/toolchains/actions:link_actions",
    ],
    args = ["-march=rv32imc_zba_zbb_zbc_zbs"],
    requires_any_of = [":constraint_bitmanip"],
)

cc_args(
    name = "arch_rv32imc",
    actions = [
        "@rules_cc//cc/toolchains/actions:compile_actions",
        "@rules_cc//cc/toolchains/actions:link_actions",
    ],
    args = ["-march=rv32imc"],
    requires_any_of = [":constraint_no_bitmanip"],
)

cc_args(
    name = "abi",
    actions = [
        "@rules_cc//cc/toolchains/actions:compile_actions",
        "@rules_cc//cc/toolchains/actions:link_actions",
    ],
    args = [
        "-mabi=ilp32",
        "-mcmodel=medany",
        "-mlittle-endian",
    ],
)

# Mirrors `:arch_rv32imcb`; the only differences are the two the ISA requires,
# `i` becoming `e` and `xcheriot` being added.
cc_args(
    name = "arch_cheriot",
    actions = [
        "@rules_cc//cc/toolchains/actions:compile_actions",
        "@rules_cc//cc/toolchains/actions:link_actions",
    ],
    args = [
        "--target=riscv32-unknown-unknown",
        "-march=rv32emc_zba_zbb_zbc_zbs_xcheriot",
    ],
    requires_any_of = [":constraint_bitmanip"],
)

# The counterpart of `:arch_rv32imc`: same thing without the bitmanip
# extensions.
cc_args(
    name = "arch_cheriot_no_bitmanip",
    actions = [
        "@rules_cc//cc/toolchains/actions:compile_actions",
        "@rules_cc//cc/toolchains/actions:link_actions",
    ],
    args = [
        "--target=riscv32-unknown-unknown",
        "-march=rv32emc_xcheriot",
    ],
    requires_any_of = [":constraint_no_bitmanip"],
)

# Not `-mabi=cheriot`, which is the CHERIoT RTOS compartment ABI and expects a
# loader to resolve cross-compartment calls.
cc_args(
    name = "abi_cheriot",
    actions = [
        "@rules_cc//cc/toolchains/actions:compile_actions",
        "@rules_cc//cc/toolchains/actions:link_actions",
    ],
    args = [
        "-mabi=cheriot-baremetal",
        "-mcmodel=medany",
        "-mlittle-endian",
    ],
)

# NOTE: please keep this list of warnings in sync with the warnings in
# `compile_flags.txt` so that `clangd` can see them.
cc_args(
    name = "warnings",
    actions = ["@rules_cc//cc/toolchains/actions:compile_actions"],
    args = [
        "-Wall",
        "-Wconversion",
        "-Wextra",
        "-Wgnu",
        "-Wimplicit-fallthrough",
        "-Winvalid-pch",
        "-Wno-covered-switch-default",
        "-Wno-error=unused-function",
        "-Wno-gnu-empty-initializer",
        "-Wno-gnu-statement-expression-from-macro-expansion",
        "-Wno-gnu-zero-variadic-macro-arguments",
        "-Wno-missing-field-initializers",
        "-Wno-sign-compare",
        "-Wno-unused-parameter",
        "-Wno-zero-length-array",
        "-Wstrict-prototypes",
        "-Wswitch-default",
        "-Wtype-limits",
        "-Wno-gnu-auto-type",
        "-Wsign-conversion",
        "-menable-experimental-extensions",
    ],
)

# Feature which turns all warnings into fatal errors.
cc_feature(
    name = "feat_warnings_as_errors",
    args = [":warnings_as_errors"],
    feature_name = "warnings_as_errors",
)

cc_args(
    name = "warnings_as_errors",
    actions = ["@rules_cc//cc/toolchains/actions:compile_actions"],
    args = ["-Werror"],
)

cc_args(
    name = "reproducible",
    actions = ["@rules_cc//cc/toolchains/actions:compile_actions"],
    args = ["-Werror=date-time"],
)

cc_feature(
    name = "feat_guards",
    args = [":guards"],
    feature_name = "guards",
)

cc_args(
    name = "guards",
    actions = ["@rules_cc//cc/toolchains/actions:compile_actions"],
    args = ["-mguards"],
)

cc_feature(
    name = "feat_coverage",
    args = [
        ":coverage_indicator_cc",
        ":coverage_indicator_ld",
        ":coverage_profile",
        ":coverage_single_byte",
        ":sha1_build_id",
    ],
    overrides = "@rules_cc//cc/toolchains/features/legacy:coverage",
)

cc_args(
    name = "coverage_single_byte",
    actions = ["@rules_cc//cc/toolchains/actions:compile_actions"],
    args = [
        "-mllvm",
        "--enable-single-byte-coverage",
    ],
)

cc_args(
    name = "coverage_profile",
    actions = [
        "@rules_cc//cc/toolchains/actions:compile_actions",
        "@rules_cc//cc/toolchains/actions:link_actions",
    ],
    args = [
        "-fprofile-instr-generate",
        "-fcoverage-mapping",
    ],
)

cc_args(
    name = "coverage_indicator_cc",
    actions = ["@rules_cc//cc/toolchains/actions:compile_actions"],
    args = ["-DOT_COVERAGE_INSTRUMENTED=1"],
)

cc_args(
    name = "coverage_indicator_ld",
    actions = ["@rules_cc//cc/toolchains/actions:link_actions"],
    args = ["-Wl,--defsym=_ot_coverage_instrumented=1"],
)

cc_args(
    name = "sha1_build_id",
    actions = ["@rules_cc//cc/toolchains/actions:link_actions"],
    args = ["-Wl,--build-id=sha1"],
)

cc_feature(
    name = "feat_use_lld",
    args = [":use_lld"],
    feature_name = "use_lld",
)

cc_args(
    name = "use_lld",
    actions = ["@rules_cc//cc/toolchains/actions:link_actions"],
    args = ["-fuse-ld=lld"],
)

cc_feature(
    name = "feat_lto",
    args = [":lto"],
    feature_name = "lto",
)

cc_args(
    name = "lto",
    actions = [
        "@rules_cc//cc/toolchains/actions:compile_actions",
        "@rules_cc//cc/toolchains/actions:link_actions",
    ],
    args = ["-flto"],
)

cc_args(
    name = "unique_sections",
    actions = ["@rules_cc//cc/toolchains/actions:compile_actions"],
    args = [
        "-ffunction-sections",
        "-fdata-sections",
    ],
)

cc_args(
    name = "gc_sections",
    actions = ["@rules_cc//cc/toolchains/actions:link_actions"],
    args = ["-Wl,--gc-sections"],
)

cc_args_list(
    name = "symbol_garbage_collection",
    args = [
        ":unique_sections",
        ":gc_sections",
    ],
)

cc_args(
    name = "constructor_destructor",
    actions = ["@rules_cc//cc/toolchains/actions:compile_actions"],
    args = [
        # Indicate that this program may not necessarily be able to use standard system calls.
        "-ffreestanding",
        # Instantiate global variables only once.
        "-fno-common",
    ],
)

# Strip local `.L` symbols at link time:
cc_args(
    name = "discard_locals",
    actions = ["@rules_cc//cc/toolchains/actions:link_actions"],
    args = ["-Wl,--discard-locals"],
)

filegroup(
    name = "doc_files",
    srcs = ["README.md"],
)

cc_feature(
    name = "feat_no_jump_tables",
    args = [":no_jump_tables_args"],
    feature_name = "no_jump_tables",
)

cc_args(
    name = "no_jump_tables_args",
    actions = ["@rules_cc//cc/toolchains/actions:compile_actions"],
    args = ["-fno-jump-tables"],
)
