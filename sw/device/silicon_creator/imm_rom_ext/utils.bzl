# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load("@lowrisc_opentitan//rules:rv.bzl", "rv_rule")

def _bin_to_imm_rom_ext_object_impl(ctx):
    cc_toolchain = find_cc_toolchain(ctx)
    outputs = []
    for src in ctx.files.srcs:
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
            executable = cc_toolchain.objcopy_executable,
        )
        outputs.append(object)
    return [DefaultInfo(files = depset(outputs), runfiles = ctx.runfiles(files = outputs))]

bin_to_imm_rom_ext_object = rv_rule(
    implementation = _bin_to_imm_rom_ext_object_impl,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
    },
    toolchains = ["@rules_cc//cc:toolchain_type"],
)

def imm_rom_ext_section(name, srcs):
    object_target_name = name + "_object"
    bin_to_imm_rom_ext_object(name = object_target_name, srcs = srcs)
    native.cc_import(
        name = name,
        objects = [object_target_name],
        data = [object_target_name],
        alwayslink = 1,
    )
