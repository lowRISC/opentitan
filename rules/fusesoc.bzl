# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@nonhermetic//:env.bzl", "ENV")

"""Rules for running FuseSoC.

FuseSoC is a package manager and set of build tools for HDL code.

Because we want the output of some FuseSoC built resources to be
available to bazel (such as the verilated chip model for running
tests), the `fusesoc_build` rule allows bazel to delegate certain
targets to FuseSoC.

This rule is not sandboxed, as our current configuration depends
on FuseSoC and its dependencies (verible, verilator, etc) already
having been installed.  In the future, we will try to rework our
dependencies so the FuseSoC rules can be sandboxed.
"""

def _fusesoc_build_impl(ctx):
    dirname = "build.{}".format(ctx.label.name)
    out_dir = ctx.actions.declare_directory(dirname)
    flags = [ctx.expand_location(f, ctx.attr.srcs) for f in ctx.attr.flags]
    outputs = [out_dir]
    groups = {}
    for group, files in ctx.attr.output_groups.items():
        deps = [ctx.actions.declare_file("{}/{}".format(dirname, f)) for f in files]
        outputs.extend(deps)
        groups[group] = depset(deps)

    ctx.actions.run(
        mnemonic = "FuseSoC",
        outputs = outputs,
        inputs = ctx.files.srcs + ctx.files.cores,
        arguments = [
            "--cores-root={}".format(c.dirname)
            for c in ctx.files.cores
        ] + [
            "run",
            "--flag=fileset_top",
            "--target={}".format(ctx.attr.target),
            "--setup",
            "--build",
            "--build-root={}".format(out_dir.path),
        ] + ctx.attr.systems + flags,
        executable = "fusesoc",
        use_default_shell_env = False,
        execution_requirements = {
            "no-sandbox": "",
        },
        env = ENV,
    )
    return [
        DefaultInfo(
            files = depset(outputs),
            data_runfiles = ctx.runfiles(files = outputs + ctx.files.data),
        ),
        OutputGroupInfo(**groups),
    ]

fusesoc_build = rule(
    implementation = _fusesoc_build_impl,
    attrs = {
        "cores": attr.label_list(allow_files = True, doc = "FuseSoC core specification files"),
        "srcs": attr.label_list(allow_files = True, doc = "Source files"),
        "data": attr.label_list(allow_files = True, doc = "Files needed at runtime"),
        "target": attr.string(mandatory = True, doc = "Target name (e.g. 'sim')"),
        "systems": attr.string_list(mandatory = True, doc = "Systems to build"),
        "flags": attr.string_list(doc = "Flags controlling the FuseSOC system build"),
        "output_groups": attr.string_list_dict(
            allow_empty = True,
            doc = "Mapping of group name to lists of files in that named group",
        ),
    },
)
