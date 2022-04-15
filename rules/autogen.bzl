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
            "-o",
            header.path,
        ] + [src.path for src in ctx.files.srcs],
        executable = ctx.executable._regtool,
    )
    return [
        CcInfo(compilation_context = cc_common.create_compilation_context(
            includes = depset([header.dirname]),
            headers = depset([header]),
        )),
        DefaultInfo(files = depset([header])),
    ]

autogen_hjson_header = rule(
    implementation = _hjson_header,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
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
        inputs = ctx.files.version + ctx.files._tool,
        arguments = [
            "-o",
            header.dirname,
            "--ot_version_file",
            ctx.files.version[0].path,
        ],
        executable = ctx.files._tool[0],
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
        "version": attr.label(default = "//util:ot_version_file", allow_files = True),
        "_tool": attr.label(default = "//util:rom_chip_info.py", allow_files = True),
    },
)

def _otp_image(ctx):
    output = ctx.actions.declare_file(ctx.attr.name + ".vmem")
    ctx.actions.run(
        outputs = [output],
        inputs = ctx.files.src + ctx.files.deps + ctx.files._tool,
        arguments = [
            "--quiet",
            "--img-cfg",
            ctx.files.src[0].path,
            "--out",
            output.path,
        ],
        executable = ctx.files._tool[0],
    )
    return [DefaultInfo(files = depset([output]), data_runfiles = ctx.runfiles(files = [output]))]

otp_image = rule(
    implementation = _otp_image,
    attrs = {
        "src": attr.label(allow_files = True),
        "deps": attr.label_list(allow_files = True),
        "_tool": attr.label(default = "//util/design:gen-otp-img.py", allow_files = True),
    },
)
