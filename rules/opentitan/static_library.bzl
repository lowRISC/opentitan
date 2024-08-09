# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Provides a rule that outputs a monolithic static library."""

# Inspired by:
# https://gist.github.com/shareefj/4e314b16148fded3a8ec874e71b07143

load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load("@lowrisc_opentitan//rules:rv.bzl", "rv_rule")

def _ot_static_library_impl(ctx):
    output_lib = ctx.actions.declare_file("lib{}.a".format(ctx.attr.name))
    output_flags = ctx.actions.declare_file("lib{}.link".format(ctx.attr.name))

    cc_toolchain = find_cc_toolchain(ctx)

    # Aggregate linker inputs of all dependencies
    lib_sets = []
    for dep in ctx.attr.deps:
        lib_sets.append(dep[CcInfo].linking_context.linker_inputs)
    input_depset = depset(transitive = lib_sets)

    # Collect user link flags and make sure they are unique
    unique_flags = {}
    for inp in input_depset.to_list():
        unique_flags.update({
            flag: None
            for flag in inp.user_link_flags
        })
    link_flags = unique_flags.keys()

    # Collect static libraries
    libs = []
    for inp in input_depset.to_list():
        for lib in inp.libraries:
            if lib.pic_static_library:
                libs.append(lib.pic_static_library)
            elif lib.static_library:
                libs.append(lib.static_library)

    lib_paths = [lib.path for lib in libs]

    ar_path = cc_toolchain.ar_executable

    ctx.actions.run_shell(
        command = "\"{0}\" rcT {1} {2} && echo -e 'create {1}\naddlib {1}\nsave\nend' | \"{0}\" -M".format(
            ar_path,
            output_lib.path,
            " ".join(lib_paths),
        ),
        inputs = libs + cc_toolchain.all_files.to_list(),
        outputs = [output_lib],
        mnemonic = "ArMerge",
        progress_message = "Merging static library {}".format(output_lib.path),
    )

    # TODO(cfrantz): do we need to collect the linker flags and emit them in a
    # separate output file?
    ctx.actions.write(
        output = output_flags,
        content = "\n".join(link_flags) + "\n",
    )
    return [
        DefaultInfo(files = depset([output_lib])),
        OutputGroupInfo(library = depset([output_lib]), linker_flags = depset([output_flags])),
    ]

ot_static_library = rv_rule(
    implementation = _ot_static_library_impl,
    attrs = {
        "deps": attr.label_list(),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
    },
    #incompatible_use_toolchain_transition = True,
    fragments = ["cpp"],
    toolchains = ["@rules_cc//cc:toolchain_type"],
)
