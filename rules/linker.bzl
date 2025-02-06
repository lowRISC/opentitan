# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rules for declaring linker scripts and linker script fragments."""

load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load("@rules_cc//cc:action_names.bzl", "C_COMPILE_ACTION_NAME")

def _preprocess_linker_file(ctx):
    cc_toolchain = find_cc_toolchain(ctx)
    features = cc_common.configure_features(
        ctx = ctx,
        cc_toolchain = cc_toolchain,
        requested_features = ctx.features,
        unsupported_features = ctx.disabled_features,
    )
    compilation_context = cc_common.merge_compilation_contexts(
        compilation_contexts = [dep[CcInfo].compilation_context for dep in ctx.attr.deps],
    )

    # FIXME could not get cc_common.compile to work because it returns no object.
    cxx_compiler_path = cc_common.get_tool_for_action(
        feature_configuration = features,
        action_name = C_COMPILE_ACTION_NAME,
    )
    c_compile_variables = cc_common.create_compile_variables(
        feature_configuration = features,
        cc_toolchain = cc_toolchain,
        user_compile_flags = ctx.fragments.cpp.copts + ctx.fragments.cpp.conlyopts,
        include_directories = compilation_context.includes,
        quote_include_directories = compilation_context.quote_includes,
        system_include_directories = compilation_context.system_includes,
        preprocessor_defines = depset(ctx.attr.defines, transitive = [compilation_context.defines]),
    )
    cmd_line = cc_common.get_memory_inefficient_command_line(
        feature_configuration = features,
        action_name = C_COMPILE_ACTION_NAME,
        variables = c_compile_variables,
    )
    env = cc_common.get_environment_variables(
        feature_configuration = features,
        action_name = C_COMPILE_ACTION_NAME,
        variables = c_compile_variables,
    )
    output_script = ctx.actions.declare_file(ctx.label.name + ".ld")
    ctx.actions.run(
        outputs = [output_script],
        inputs = depset(
            [ctx.file.script],
            transitive = [compilation_context.headers, cc_toolchain.all_files],
        ),
        executable = cxx_compiler_path,
        arguments = [
            "-E",  # Preprocess only.
            "-P",  # Avoid line markers in output.
            "-C",  # Keep comments
            "-xc",  # Force C language.
            ctx.file.script.path,
            "-o",
            output_script.path,
        ] + cmd_line,
        env = env,
    )
    return output_script

def _ld_library_impl(ctx):
    user_link_flags = []
    files = []

    if ctx.attr.non_page_aligned_segments:
        user_link_flags += [
            "-Wl,-nmagic",
        ]

    files += ctx.files.includes
    user_link_flags += [
        "-Wl,-L,{}".format(include.dirname)
        for include in ctx.files.includes
    ]

    if ctx.file.script:
        output_script = _preprocess_linker_file(ctx)
        files.append(output_script)

        user_link_flags += [
            "-Wl,-T,{}".format(output_script.path),
        ]

    return [
        DefaultInfo(
            files = depset(files),
        ),
        cc_common.merge_cc_infos(
            # Order is important! We list dependencies first so that any
            # linker flags set by dependencies (such as -Wl,-L) appear before
            # the files that depend on them.
            cc_infos = [dep[CcInfo] for dep in ctx.attr.deps] + [CcInfo(
                linking_context = cc_common.create_linking_context(
                    linker_inputs = depset([cc_common.create_linker_input(
                        owner = ctx.label,
                        additional_inputs = depset(files),
                        user_link_flags = depset(user_link_flags),
                    )]),
                ),
                compilation_context = cc_common.create_compilation_context(
                    defines = depset(ctx.attr.defines),
                    headers = depset(ctx.files.includes),
                    includes = depset([f.dirname for f in ctx.files.includes]),
                ),
            )],
        ),
    ]

ld_library = rule(
    implementation = _ld_library_impl,
    fragments = ["cpp"],
    doc = """
    A linker script library. Linker script libraries consist of a collection of
    "includes" (the linker equivalent of a header) and an optional script. Linker
    script libraries can depend on other libraries to access the includes they
    publish; cc_binaries can depend on an ld_library with a script to specify it
    as the linker script for that binary.

    At most one ld_library in a cc_binary's dependencies may have a script.

    If non_page_aligned_segments is used, instruct the linker to turn off page
    alignment for segments and not to include the headers in the first segment
    (this is the -nmagic option of GNU ld). See https://reviews.llvm.org/D61201
    for more details.
    """,
    attrs = {
        "script": attr.label(
            allow_single_file = True,
            doc = "Main linker script. This file will be preprocessed.",
        ),
        "defines": attr.string_list(
            doc = "C preprocessor defines. These defines are subject to Make variable substitution.",
        ),
        "includes": attr.label_list(
            default = [],
            allow_files = True,
            doc = """
                Link script libraries. Those files will automatically be added
                to the linker search paths and will also be available in the
                preprocessing context of the main link script.
                """,
        ),
        "deps": attr.label_list(
            default = [],
            providers = [CcInfo],
        ),
        "non_page_aligned_segments": attr.bool(
            default = False,
        ),
    },
    toolchains = ["@rules_cc//cc:toolchain_type"],
)
