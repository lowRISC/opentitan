# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_cc//cc:action_names.bzl", "OBJ_COPY_ACTION_NAME")
load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load("@lowrisc_opentitan//rules:rv.bzl", "rv_rule")

def _bin_to_imm_section_object_impl(ctx):
    cc_toolchain = find_cc_toolchain(ctx)
    feature_config = cc_common.configure_features(
        ctx = ctx,
        cc_toolchain = cc_toolchain,
        requested_features = ctx.features,
        unsupported_features = ctx.disabled_features,
    )
    objcopy = cc_common.get_tool_for_action(
        feature_configuration = feature_config,
        action_name = OBJ_COPY_ACTION_NAME,
    )

    for src in ctx.files.src:
        if src.extension != "bin":
            continue
        object = ctx.actions.declare_file(
            "{}.{}".format(
                src.basename.replace("." + src.extension, ""),
                "o",
            ),
        )
        ctx.actions.run(
            outputs = [object],
            inputs = [src] + cc_toolchain.all_files.to_list(),
            arguments = [
                "-I",
                "binary",
                "-O",
                "elf32-littleriscv",
                "--rename-section",
                ".data=.rom_ext_immutable,alloc,load,readonly,data,contents",
                src.path,
                object.path,
            ],
            executable = objcopy,
        )

        # e2e/exec_env tests ensure the immutable rom_ext is the same across all
        # exec env, so simply return the first one.
        outputs = [object]
        return [
            DefaultInfo(
                files = depset(outputs),
                runfiles = ctx.runfiles(files = outputs),
            ),
        ]

bin_to_imm_section_object = rv_rule(
    implementation = _bin_to_imm_section_object_impl,
    attrs = {
        "src": attr.label(allow_files = True),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
    },
    fragments = ["cpp"],
    toolchains = ["@rules_cc//cc:toolchain_type"],
)

def create_imm_section_targets(name, src):
    object_target_name = name + "_object"
    bin_to_imm_section_object(
        name = object_target_name,
        src = src,
    )
    native.cc_import(
        name = name,
        objects = [object_target_name],
        data = [object_target_name],
        alwayslink = 1,
    )
