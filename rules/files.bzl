# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def _exclude_files_impl(ctx):
    out = []
    for src in ctx.files.srcs:
        include = True
        for suffix in ctx.attr.exclude_suffix:
            if src.path.endswith(suffix):
                include = False
                break
        if include:
            out.append(src)
    return [DefaultInfo(files = depset(out))]

exclude_files = rule(
    implementation = _exclude_files_impl,
    attrs = {
        "srcs": attr.label_list(
            allow_files = True,
            mandatory = True,
            doc = "Targets producing file outputs",
        ),
        "exclude_suffix": attr.string_list(
            doc = "File suffixes to exclude from the result",
        ),
    },
)

def _output_groups(ctx):
    out = []
    for src in ctx.attr.srcs:
        src = src[OutputGroupInfo]
        for group in ctx.attr.groups:
            out.append(src[group])
    return DefaultInfo(
        files = depset(transitive = out),
    )

output_groups = rule(
    implementation = _output_groups,
    attrs = {
        "srcs": attr.label_list(
            mandatory = True,
            providers = [OutputGroupInfo],
            doc = "Targets producing file outputs",
        ),
        "groups": attr.string_list(
            doc = "Output groups to collect from the srcs",
        ),
    },
)
