# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_cc//cc:action_names.bzl", "OBJ_COPY_ACTION_NAME")
load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load("@lowrisc_opentitan//rules:rv.bzl", "rv_rule")
load("@lowrisc_opentitan//rules/opentitan:exec_env.bzl", "ExecEnvInfo")

def _bin_to_imm_rom_ext_object_impl(ctx):
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

    outputs = []
    exec_env_name = ctx.attr.exec_env[ExecEnvInfo].exec_env
    for src in ctx.attr.src.output_groups[exec_env_name + "_binary"].to_list():
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
        outputs.append(object)
    if len(outputs) != 1:
        fail("Generated zero or more than one binary: {}".format(outputs))
    return [
        DefaultInfo(
            files = depset(outputs),
            runfiles = ctx.runfiles(files = outputs),
        ),
    ]

bin_to_imm_rom_ext_object = rv_rule(
    implementation = _bin_to_imm_rom_ext_object_impl,
    attrs = {
        "src": attr.label(allow_files = True),
        "exec_env": attr.label(
            providers = [ExecEnvInfo],
            doc = "The execution environment for this target.",
        ),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
    },
    fragments = ["cpp"],
    toolchains = ["@rules_cc//cc:toolchain_type"],
)

def create_imm_rom_ext_targets(src, exec_env, base_name):
    exec_env_name = Label(exec_env).name
    object_target_name = "{}_{}_object".format(base_name, exec_env_name)
    cc_import_name = "{}_{}".format(base_name, exec_env_name)
    bin_to_imm_rom_ext_object(
        name = object_target_name,
        src = src,
        exec_env = exec_env,
    )
    native.cc_import(
        name = cc_import_name,
        objects = [object_target_name],
        data = [object_target_name],
        alwayslink = 1,
    )
