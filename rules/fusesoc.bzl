# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@nonhermetic//:env.bzl", "ENV")
load("@ot_python_deps//:requirements.bzl", "entry_point")

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

load("@bazel_skylib//rules:common_settings.bzl", "BuildSettingInfo")

def _corefiles2rootarg(core):
    return core.dirname

def _fusesoc_build_impl(ctx):
    dirname = "build.{}".format(ctx.label.name)
    out_dir = ctx.actions.declare_directory(dirname)
    flags = [ctx.expand_location(f, ctx.attr.srcs) for f in ctx.attr.flags]
    outputs = [out_dir]
    groups = {}
    args = ctx.actions.args()

    for group, files in ctx.attr.output_groups.items():
        deps = [ctx.actions.declare_file("{}/{}".format(dirname, f)) for f in files]
        outputs.extend(deps)
        groups[group] = depset(deps)

    if ctx.attr.verilator_options:
        verilator_options = ctx.attr.verilator_options[BuildSettingInfo].value
        flags.append("--verilator_options={}".format(" ".join(verilator_options)))

    if ctx.attr.make_options:
        make_options = ctx.attr.make_options[BuildSettingInfo].value
        flags.append("--make_options={}".format(" ".join(make_options)))

    args.add_all(
        ctx.files.cores,
        uniquify = True,
        map_each = _corefiles2rootarg,
        format_each = "--cores-root=%s",
    )

    args.add_all([
        "--verbose",
        "run",
        "--flag=fileset_top",
    ])
    args.add(ctx.attr.target, format = "--target=%s")
    args.add_all([
        "--setup",
        "--build",
    ])
    args.add(out_dir.path, format = "--build-root=%s")

    args.add_all(ctx.attr.systems)
    args.add_all(flags)

    # Note: the `fileset_top` flag used above is specific to the OpenTitan
    # project to select the correct RTL fileset.
    ctx.actions.run(
        mnemonic = "FuseSoC",
        outputs = outputs,
        inputs = ctx.files.srcs + ctx.files.cores + ctx.files._fusesoc,
        arguments = [args],
        executable = ctx.executable._fusesoc,
        use_default_shell_env = False,
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
        "verilator_options": attr.label(),
        "make_options": attr.label(),
        "_fusesoc": attr.label(
            default = "//util:fusesoc_build",
            executable = True,
            cfg = "exec",
        ),
    },
)
