# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@nonhermetic//:env.bzl", "ENV")

"""Rules for memory splicing with Vivado.
"""

def _bitstream_splice_impl(ctx):
    update = ctx.actions.declare_file("{}.update.mem".format(ctx.label.name))
    spliced = ctx.actions.declare_file("{}.spliced.bit".format(ctx.label.name))
    output = ctx.actions.declare_file("{}.bit".format(ctx.label.name))

    ctx.actions.run(
        mnemonic = "GenVivadoImage",
        outputs = [update],
        inputs = [ctx.executable._gen_mem_img, ctx.file.data],
        arguments = [
            ctx.file.data.path,
            update.path,
        ] + (["--swap-nibbles"] if ctx.attr.swap_nybbles else []),
        executable = ctx.executable._gen_mem_img,
        use_default_shell_env = True,
        execution_requirements = {
            "no-sandbox": "",
        },
    )

    # Vivado's `updatemem` only accepts bitstream filenames that end with
    # ".bit". If the `src` bitstream came from the GCP bucket, its filename will
    # end with ".bit.splice" or ".bit.orig" and `updatemem` would reject it.
    #
    # TODO(#13807) Eliminate this symlink step once the names of cached
    # bitstream files are guaranteed to end with ".bit".
    tmpsrc = ctx.actions.declare_file("{}.tmpsrc.bit".format(ctx.label.name))
    ctx.actions.symlink(output = tmpsrc, target_file = ctx.file.src)

    ctx.actions.run(
        mnemonic = "SpliceBitstream",
        outputs = [spliced],
        inputs = [tmpsrc, ctx.file.meminfo, update],
        arguments = [
            "-force",
            "--meminfo",
            ctx.file.meminfo.path,
            "--data",
            update.path,
            "--bit",
            tmpsrc.path,
            "--proc",
            "dummy",
            "--out",
            spliced.path,
        ] + ["--debug"] if ctx.attr.debug else [],
        executable = "updatemem",
        use_default_shell_env = False,
        execution_requirements = {
            "no-sandbox": "",
        },
        env = ENV,
    )

    if ctx.attr.update_usr_access:
        ctx.actions.run(
            mnemonic = "UpdateUsrAccessValue",
            outputs = [output],
            inputs = [spliced],
            arguments = [
                "--rcfile=",
                "--logging=info",
                "fpga",
                "update-usr-access",
                spliced.path,
                output.path,
            ],
            executable = ctx.executable._opentitantool,
        )
    else:
        ctx.actions.symlink(
            output = output,
            target_file = spliced,
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
        "update_usr_access": attr.bool(default = False, doc = "Update the USR_ACCESS value of the bitstream, breaks hermeticity"),
        "_gen_mem_img": attr.label(
            default = "//hw/ip/rom_ctrl/util:gen_vivado_mem_image",
            executable = True,
            cfg = "exec",
        ),
        "_opentitantool": attr.label(
            default = "//sw/host/opentitantool:opentitantool",
            executable = True,
            cfg = "exec",
        ),
    },
)
