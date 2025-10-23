# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:providers.bzl",
    "SiliconBinaryInfo",
    "get_one_binary_file",
)
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load(
    "@rules_cc//cc:action_names.bzl",
    "CPP_LINK_STATIC_LIBRARY_ACTION_NAME",
    "OBJ_COPY_ACTION_NAME",
)
load("@lowrisc_opentitan//rules:rv.bzl", "rv_rule")
load(
    "//sw/device/silicon_creator/rom_ext/imm_section:defs.bzl",
    "IMM_SECTION_VERSION",
)

def _cc_import(ctx, cc_toolchain, object):
    feature_configuration = cc_common.configure_features(
        ctx = ctx,
        cc_toolchain = cc_toolchain,
    )
    ar = cc_common.get_tool_for_action(
        feature_configuration = feature_configuration,
        action_name = CPP_LINK_STATIC_LIBRARY_ACTION_NAME,
    )

    lib_name = "lib" + ctx.label.name + ".a"
    static_library = ctx.actions.declare_file(lib_name)
    ctx.actions.run(
        outputs = [static_library],
        inputs = [object] + cc_toolchain.all_files.to_list(),
        arguments = ["-rcs", static_library.path, object.path],
        executable = ar,
    )

    library_to_link = cc_common.create_library_to_link(
        actions = ctx.actions,
        feature_configuration = feature_configuration,
        cc_toolchain = cc_toolchain,
        static_library = static_library,
        alwayslink = True,
    )

    cc_info = CcInfo(
        linking_context = cc_common.create_linking_context(
            linker_inputs = depset([
                cc_common.create_linker_input(
                    libraries = depset([library_to_link]),
                    owner = ctx.label,
                ),
            ]),
        ),
    )

    return static_library, cc_info

def _choose_one_build(src):
    # Returns binary_file, [Runfiles]

    if type(src) == "File":
        return src, []

    # e2e/exec_env tests ensure the immutable rom_ext is the same across all
    # exec env.
    bin = get_one_binary_file(src, field = "binary", providers = [SiliconBinaryInfo])
    elf = get_one_binary_file(src, field = "elf", providers = [SiliconBinaryInfo])
    return bin, [elf]

def _create_imm_section_targets_impl(ctx):
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

    src, runfiles = _choose_one_build(ctx.attr.src)

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

    lib, cc_info = _cc_import(ctx, cc_toolchain, object)

    return [
        DefaultInfo(
            files = depset([lib]),
            runfiles = ctx.runfiles(files = runfiles),
        ),
        cc_info,
    ]

create_imm_section_targets = rv_rule(
    implementation = _create_imm_section_targets_impl,
    attrs = {
        "src": attr.label(allow_files = True),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
    },
    fragments = ["cpp"],
    provides = [CcInfo],
    toolchains = ["@rules_cc//cc:toolchain_type"],
)

_RELEASE_BUILD_HEADER = """\
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//sw/device/silicon_creator/rom_ext/imm_section:utils.bzl",
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
            default = "//util:gen_stamped_tarball",
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
