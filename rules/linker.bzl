# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rules for declaring linker scripts and linker script fragments."""

def _ld_library_impl(ctx):
    files = [] + ctx.files.includes
    user_link_flags = []

    # Disable non-volatile scratch region and counters if building for english
    # breakfast. This should appear before the linker script.
    if "-DOT_IS_ENGLISH_BREAKFAST_REDUCED_SUPPORT_FOR_INTERNAL_USE_ONLY_" in ctx.fragments.cpp.copts:
        user_link_flags += [
            "-Wl,--defsym=no_ottf_nv_scratch=1",
            "-Wl,--defsym=no_ottf_nv_counter=1",
        ]
    if ctx.attr.non_page_aligned_segments:
        user_link_flags += [
            "-Wl,-nmagic",
        ]

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
        "script": attr.label(allow_single_file = True),
        "includes": attr.label_list(
            default = [],
            allow_files = True,
        ),
        "deps": attr.label_list(
            default = [],
            providers = [CcInfo],
        ),
        "non_page_aligned_segments": attr.bool(
            default = False,
        ),
    },
)
