# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

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
    out_dir = ctx.actions.declare_directory("build.{}".format(ctx.label.name))
    ctx.actions.run(
        mnemonic = "FuseSoC",
        outputs = [out_dir],
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
        ] + ctx.attr.systems,
        executable = "fusesoc",
        use_default_shell_env = True,
        execution_requirements = {
            "no-sandbox": "",
        },
    )
    return [DefaultInfo(
        files = depset([out_dir]),
        data_runfiles = ctx.runfiles(files = [out_dir]),
    )]

fusesoc_build = rule(
    implementation = _fusesoc_build_impl,
    attrs = {
        "cores": attr.label_list(allow_files = True, doc = "FuseSoC core specification files"),
        "srcs": attr.label_list(allow_files = True, doc = "Source files"),
        "target": attr.string(mandatory = True, doc = "Target name (e.g. 'sim')"),
        "systems": attr.string_list(mandatory = True, doc = "Systems to build"),
    },
)
