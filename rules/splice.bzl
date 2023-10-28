# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@nonhermetic//:env.bzl", "ENV")
load("//rules/opentitan:splice.bzl", "splice_bitstream")

"""Rules for memory splicing with Vivado.
"""

def _bitstream_splice_impl(ctx):
    output = splice_bitstream(
        ctx,
        ENV,
        ctx.attr.name,
        ctx.file.src,
        [ctx.file.meminfo],
        [ctx.file.data],
        ctx.attr._gen_mem_img.files_to_run,
        ctx.attr._opentitantool.files_to_run,
        ctx.executable._splice,
    )
    return DefaultInfo(
        files = depset([output]),
        data_runfiles = ctx.runfiles(files = [output]),
    )

bitstream_splice_ = rule(
    implementation = _bitstream_splice_impl,
    attrs = {
        "meminfo": attr.label(allow_single_file = True, doc = "Memory layout info file (an .mmi file)"),
        "src": attr.label(allow_single_file = True, doc = "The bitstream to splice"),
        "data": attr.label(allow_single_file = True, doc = "The memory image to splice into the bitstream"),
        "debug": attr.bool(default = False, doc = "Emit debug info while updating"),
        "update_usr_access": attr.bool(default = False, doc = "Update the USR_ACCESS value of the bitstream, breaks hermeticity (deprecated)"),
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
        "_splice": attr.label(
            default = "//util/fpga:splice",
            executable = True,
            cfg = "exec",
        ),
    },
)

def bitstream_splice(testonly = True, **kwargs):
    bitstream_splice_(testonly = testonly, **kwargs)
