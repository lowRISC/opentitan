# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Autogeneration rules for OpenTitan.

The rules in this file are for autogenerating various file resources
used by the OpenTitan build, such as register definition files generated
from hjson register descriptions.
"""

def _hjson_header(ctx):
    header = ctx.actions.declare_file("{}.h".format(ctx.label.name))
    ctx.actions.run(
        outputs = [header],
        inputs = ctx.files.srcs + [ctx.executable._regtool],
        arguments = [
            "-D",
            "-q",
            "-o",
            header.path,
        ] + [src.path for src in ctx.files.srcs],
        executable = ctx.executable._regtool,
    )

    tock = ctx.actions.declare_file("{}.rs".format(ctx.label.name))
    ctx.actions.run(
        outputs = [tock],
        inputs = ctx.files.srcs + [ctx.executable._regtool, ctx.file.version_stamp],
        arguments = [
            "--tock",
            "--version-stamp={}".format(ctx.file.version_stamp.path),
            "-q",
            "-o",
            tock.path,
        ] + [src.path for src in ctx.files.srcs],
        executable = ctx.executable._regtool,
    )

    return [
        CcInfo(compilation_context = cc_common.create_compilation_context(
            includes = depset([header.dirname]),
            headers = depset([header]),
        )),
        DefaultInfo(files = depset([header, tock])),
        OutputGroupInfo(
            header = depset([header]),
            tock = depset([tock]),
        ),
    ]

autogen_hjson_header = rule(
    implementation = _hjson_header,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "version_stamp": attr.label(
            default = "//util:full_version_file",
            allow_single_file = True,
        ),
        "_regtool": attr.label(
            default = "//util:regtool",
            executable = True,
            cfg = "exec",
        ),
    },
)

def _chip_info(ctx):
    header = ctx.actions.declare_file("chip_info.h")
    ctx.actions.run(
        outputs = [header],
        inputs = [
            ctx.file.version,
            ctx.executable._tool,
        ],
        arguments = [
            "-o",
            header.dirname,
            "--ot_version_file",
            ctx.file.version.path,
        ],
        executable = ctx.executable._tool,
    )
    return [
        CcInfo(compilation_context = cc_common.create_compilation_context(
            includes = depset([header.dirname]),
            headers = depset([header]),
        )),
        DefaultInfo(files = depset([header])),
    ]

autogen_chip_info = rule(
    implementation = _chip_info,
    attrs = {
        "version": attr.label(
            default = "//util:ot_version_file",
            allow_single_file = True,
        ),
        "_tool": attr.label(
            default = "//util:rom_chip_info",
            executable = True,
            cfg = "exec",
        ),
    },
)

def _otp_image(ctx):
    # TODO(dmcardle) I don't like hardcoding the width in the filename. Maybe we
    # can write it into some metadata in the file instead.
    output = ctx.actions.declare_file(ctx.attr.name + ".24.vmem")
    ctx.actions.run(
        outputs = [output],
        inputs = [
            ctx.file.src,
            ctx.file.lc_state_def,
            ctx.file.mmap_def,
            ctx.executable._tool,
        ],
        arguments = [
            "--quiet",
            "--lc-state-def",
            ctx.file.lc_state_def.path,
            "--mmap-def",
            ctx.file.mmap_def.path,
            "--img-cfg",
            ctx.file.src.path,
            "--out",
            "{}/{}.BITWIDTH.vmem".format(output.dirname, ctx.attr.name),
        ],
        executable = ctx.executable._tool,
    )
    return [DefaultInfo(files = depset([output]), data_runfiles = ctx.runfiles(files = [output]))]

otp_image = rule(
    implementation = _otp_image,
    attrs = {
        "src": attr.label(allow_single_file = True),
        "lc_state_def": attr.label(
            allow_single_file = True,
            default = "//hw/ip/lc_ctrl/data:lc_ctrl_state.hjson",
            doc = "Life-cycle state definition file in Hjson format.",
        ),
        "mmap_def": attr.label(
            allow_single_file = True,
            default = "//hw/ip/otp_ctrl/data:otp_ctrl_mmap.hjson",
            doc = "OTP Controller memory map file in Hjson format.",
        ),
        "_tool": attr.label(
            default = "//util/design:gen-otp-img",
            executable = True,
            cfg = "exec",
        ),
    },
)
