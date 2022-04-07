# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rules for declaring linker scripts and linker script fragments."""

def _ld_library_impl(ctx):
    files = [] + ctx.files.fragments
    user_link_flags = []
    if ctx.file.script:
        files += ctx.files.script
        user_link_flags += [
            "-Wl,-T,{}".format(ctx.file.script.path),
        ]

    return [
        cc_common.merge_cc_infos(
            direct_cc_infos = [CcInfo(
                linking_context = cc_common.create_linking_context(
                    linker_inputs = depset([cc_common.create_linker_input(
                        owner = ctx.label,
                        additional_inputs = depset(files),
                        user_link_flags = depset(user_link_flags),
                    )]),
                ),
            )],
            cc_infos = [dep[CcInfo] for dep in ctx.attr.deps],
        ),
    ]

ld_library = rule(
    implementation = _ld_library_impl,
    doc = """
    A linker script library. Linker script libraries consist of a collection of
    "fragments" (the linker equivalent of a header) and an optional script. Linker
    script libraries can depend on other libraries to access the fragments they
    public; cc_binaries can depend on an ld_library with a script to specify it
    as the linker script for that binary.

    At most one ld_library in a cc_binary's dependencies may have a script.
    """,
    attrs = {
        "script": attr.label(allow_single_file = True),
        "fragments": attr.label_list(
            default = [],
            allow_files = True,
        ),
        "deps": attr.label_list(
            default = [],
            providers = [CcInfo],
        ),
    },
)
