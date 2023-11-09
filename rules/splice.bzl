# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@nonhermetic//:env.bzl", "ENV")
load("//rules/opentitan:toolchain.bzl", "LOCALTOOLS_TOOLCHAIN")

"""Rules for memory splicing with Vivado.
"""

def _bitstream_splice_impl(ctx):
    tc = ctx.toolchains[LOCALTOOLS_TOOLCHAIN]
    update = ctx.actions.declare_file("{}.update.mem".format(ctx.label.name))
    spliced = ctx.actions.declare_file("{}.spliced.bit".format(ctx.label.name))
    output = ctx.actions.declare_file("{}.bit".format(ctx.label.name))

    gen_mem_img_args = ctx.actions.args()
    gen_mem_img_args.add_all([ctx.file.data, update])
    if ctx.attr.swap_nybbles:
        gen_mem_img_args.add("--swap-nibbles")

    ctx.actions.run(
        mnemonic = "GenVivadoImage",
        outputs = [update],
        inputs = [ctx.file.data],
        arguments = [gen_mem_img_args],
        executable = tc.tools.gen_mem_image,
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

    updatemem_args = ctx.actions.args()
    updatemem_args.add("--force")
    updatemem_args.add("--meminfo", ctx.file.meminfo)
    updatemem_args.add("--data", update)
    updatemem_args.add("--bit", tmpsrc)
    updatemem_args.add("--proc", "dummy")
    updatemem_args.add("--out", spliced)
    if ctx.attr.debug:
        updatemem_args.add("--debug")

    ctx.actions.run(
        mnemonic = "SpliceBitstream",
        outputs = [spliced],
        inputs = [tmpsrc, ctx.file.meminfo, update],
        arguments = [updatemem_args],
        executable = "updatemem",
        use_default_shell_env = False,
        execution_requirements = {
            "no-sandbox": "",
        },
        env = ENV,
    )

    if ctx.attr.update_usr_access:
        ott_args = ctx.actions.args()
        ott_args.add_all(
            [
                "--rcfile=",
                "--logging=info",
                "fpga",
                "update-usr-access",
                spliced.path,
                output.path,
            ],
        )
        ctx.actions.run(
            mnemonic = "UpdateUsrAccessValue",
            outputs = [output],
            inputs = [spliced],
            arguments = [ott_args],
            executable = tc.tools.opentitantool,
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

bitstream_splice_ = rule(
    implementation = _bitstream_splice_impl,
    attrs = {
        "meminfo": attr.label(allow_single_file = True, doc = "Memory layout info file (an .mmi file)"),
        "src": attr.label(allow_single_file = True, doc = "The bitstream to splice"),
        "data": attr.label(allow_single_file = True, doc = "The memory image to splice into the bitstream"),
        "swap_nybbles": attr.bool(default = True, doc = "Swap nybbles while preparing the memory image"),
        "debug": attr.bool(default = False, doc = "Emit debug info while updating"),
        "update_usr_access": attr.bool(default = False, doc = "Update the USR_ACCESS value of the bitstream, breaks hermeticity"),
    },
    toolchains = [LOCALTOOLS_TOOLCHAIN],
)

def bitstream_splice(testonly = True, **kwargs):
    bitstream_splice_(testonly = testonly, **kwargs)
