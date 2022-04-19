# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@nonhermetic//:env.bzl", "ENV")

"""Rules for memory splicing with Vivado.
"""

def _bitstream_splice_impl(ctx):
    update = ctx.actions.declare_file("{}.update.mem".format(ctx.label.name))
    output = ctx.actions.declare_file("{}.bit".format(ctx.label.name))

    ctx.actions.run(
        mnemonic = "GenVivadoImage",
        outputs = [update],
        inputs = [ctx.executable._tool, ctx.file.data],
        arguments = [
            ctx.file.data.path,
            update.path,
        ] + ["--swap-nibbles"] if ctx.attr.swap_nybbles else [],
        executable = ctx.executable._tool,
        use_default_shell_env = True,
        execution_requirements = {
            "no-sandbox": "",
        },
    )

    ctx.actions.run(
        mnemonic = "SpliceBitstream",
        outputs = [output],
        inputs = [ctx.file.src, ctx.file.meminfo, update],
        arguments = [
            "-force",
            "--meminfo",
            ctx.file.meminfo.path,
            "--data",
            update.path,
            "--bit",
            ctx.file.src.path,
            "--proc",
            "dummy",
            "--out",
            output.path,
        ] + ["--debug"] if ctx.attr.debug else [],
        executable = "updatemem",
        use_default_shell_env = False,
        execution_requirements = {
            "no-sandbox": "",
        },
        env = ENV,
    )

    return [
        DefaultInfo(
            files = depset([output]),
            data_runfiles = ctx.runfiles(files = [output]),
        ),
        OutputGroupInfo(
            bitstream = depset([output]),
            update = depset([update]),
        ),
    ]

bitstream_splice = rule(
    implementation = _bitstream_splice_impl,
    attrs = {
        "meminfo": attr.label(allow_single_file = True, doc = "Memory layout info file (an .mmi file)"),
        "src": attr.label(allow_single_file = True, doc = "The bitstream to splice"),
        "data": attr.label(allow_single_file = True, doc = "The memory image to splice into the bitstream"),
        "swap_nybbles": attr.bool(default = True, doc = "Swap nybbles while preparing the memory image"),
        "debug": attr.bool(default = True, doc = "Emit debug info while updating"),
        "_tool": attr.label(
            default = "//hw/ip/rom_ctrl/util:gen_vivado_mem_image",
            executable = True,
            cfg = "exec",
        ),
    },
)
