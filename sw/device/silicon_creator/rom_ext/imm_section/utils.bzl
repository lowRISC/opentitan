# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_cc//cc:action_names.bzl", "OBJ_COPY_ACTION_NAME")
load(
    "@lowrisc_opentitan//rules/opentitan:providers.bzl",
    "SiliconBinaryInfo",
    "get_one_binary_file",
)
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load("@lowrisc_opentitan//rules:rv.bzl", "rv_rule")
load(
    "@lowrisc_opentitan//sw/device/silicon_creator/rom_ext/imm_section:defs.bzl",
    "IMM_SECTION_VERSION",
)

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

_RELEASE_BUILD_HEADER = """\
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@lowrisc_opentitan//sw/device/silicon_creator/rom_ext/imm_section:utils.bzl",
    "create_imm_section_targets",
)

package(default_visibility = ["//visibility:public"])

# Release version: {version}
"""

_RELEASE_BUILD_TARGET = """
create_imm_section_targets(
    name = "{name}",
    src = "{filename}",
)
"""

def _prepare_release_files(ctx):
    build_contents = [
        _RELEASE_BUILD_HEADER.format(version = IMM_SECTION_VERSION),
    ]
    build_file = ctx.actions.declare_file("BUILD")

    files = [build_file]
    for name, target in zip(ctx.attr.variants_keys, ctx.attr.variants_values):
        # The test //sw/device/silicon_creator/rom_ext/imm_section/e2e/exec_env/...
        # ensures the imm_section is the same across all exec env, so we only
        # release one of them (silicon_creator).
        bin = get_one_binary_file(target, field = "binary", providers = [SiliconBinaryInfo])
        files.extend([
            bin,
            get_one_binary_file(target, field = "elf", providers = [SiliconBinaryInfo]),
            get_one_binary_file(target, field = "mapfile", providers = [SiliconBinaryInfo]),
        ])
        build_contents.append(_RELEASE_BUILD_TARGET.format(name = name, filename = bin.basename))

    ctx.actions.write(build_file, "".join(build_contents))

    output = ctx.actions.declare_file("{}.tar".format(ctx.attr.name))
    ctx.actions.run(
        outputs = [output],
        inputs = files + [ctx.version_file],
        arguments = [
            "--out",
            output.path,
            "--stamp_file",
            ctx.version_file.path,
            "--version",
            IMM_SECTION_VERSION,
        ] + [f.path for f in files],
        executable = ctx.executable._tool,
    )

    return [
        DefaultInfo(files = depset([output, build_file])),
    ]

prepare_release_files = rule(
    implementation = _prepare_release_files,
    attrs = {
        "variants_keys": attr.string_list(doc = "Name of the opentitan_binary to release"),
        "variants_values": attr.label_list(doc = "Target label of the opentitan_binary to release"),
        "_tool": attr.label(
            default = "@lowrisc_opentitan//util:gen_stamped_tarball",
            executable = True,
            cfg = "exec",
        ),
    },
)

def imm_section_bundle(name, variants, **kwargs):
    prepare_release_files(
        name = name,
        variants_keys = variants.keys(),
        variants_values = variants.values(),
        **kwargs
    )
