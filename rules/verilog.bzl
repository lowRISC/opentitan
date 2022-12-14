# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def _sv_library_impl(ctx):
    transitive_deps = [dep[DefaultInfo].files for dep in ctx.attr.deps]
    deps = depset(ctx.files.deps, transitive=transitive_deps)
    srcs = ctx.files.srcs
    inputs = depset(srcs, transitive=[deps])
    return [
        DefaultInfo(files = inputs),
    ]

sv_library = rule(
    implementation = _sv_library_impl,
    attrs = {
        "srcs": attr.label_list(
            allow_files = [".sv", ".svh"],
            doc = "SystemVerilog source files",
        ),
        "deps": attr.label_list(
            doc = "Dependencies",
        ),
    },
)

def _sv_list_impl(ctx):
    deps = depset(ctx.files.deps)
    output_file = ctx.actions.declare_file(ctx.label.name + ".svlist")
    ctx.actions.write(
        output = output_file,
        content = "\n".join(
            [f.path for f in deps.to_list()]
        ),
        is_executable = False
    )
    return [
        DefaultInfo(files = depset([output_file])),
    ]


sv_list = rule(
    implementation = _sv_list_impl,
    attrs = {
        "deps": attr.label_list(
            doc = "Dependencies",
        ),
    },
)