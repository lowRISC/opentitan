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

def _cryptotest_hjson_external(ctx):
    """
    Implementation of the Bazel rule for parsing externally-sourced test vectors.

    Crypto test vectors are represented in a standard HJSON format; for
    externally-sourced vectors, we need to parse the original data into the
    standard format before it can be used.

    This rule expects an executable script (the `parser` attribute) and a
    single external data file to pass to this script (the `src` attribute). It
    assumes that the parser accepts the following syntax:
      <script> <input file> dst.hjson

    ...where <input file> is the external test data and dst.hjson is the HJSON
    file to which the script writes the test vectors.
    """

    hjson = ctx.actions.declare_file(ctx.attr.name + ".hjson")
    parser_input = ctx.file.src
    ctx.actions.run(
        outputs = [hjson],
        inputs = [ctx.executable.parser, parser_input],
        arguments = [parser_input.path, hjson.path],
        executable = ctx.executable.parser,
    )

    return [
        DefaultInfo(files = depset([hjson])),
        OutputGroupInfo(
            hjson = depset([hjson]),
        ),
    ]

autogen_cryptotest_hjson_external = rule(
    implementation = _cryptotest_hjson_external,
    attrs = {
        "deps": attr.label_list(allow_files = True),
        "src": attr.label(allow_single_file = True),
        "parser": attr.label(
            mandatory = True,
            executable = True,
            cfg = "exec",
        ),
    },
)

def _cryptotest_header(ctx):
    """
    Implementation of the Bazel rule for generating crypto test vector headers.

    Crypto tests are all represented in a standard HJSON format. This rule runs
    an algorithm-specific script (the `test_setter` attribute) that reads an
    HJSON file (the `hjson` attribute) and populates a header template (the
    `template` attribute).

    Assumes that `test_setter` scripts accept the following syntax:
      <script> --template dst.h.tpl tests.hjson dst.h

    ...where dst.h.tpl is the header template, tests.hjson is the file
    containing the HJSON test vectors and dst.h is the header file to which the
    output will be written.
    """
    template = ctx.file.template
    if not template.basename.endswith(".h.tpl"):
        fail("Expected template to have a `.h.tpl` extension, got: " + str(ctx.files.srcs))
    header = ctx.actions.declare_file("{}/{}".format(ctx.label.name, template.basename[:-4]))

    hjson = ctx.file.hjson
    ctx.actions.run(
        outputs = [header],
        inputs = [ctx.executable.test_setter, template, hjson],
        arguments = ["--template", template.path, hjson.path, header.path],
        executable = ctx.executable.test_setter,
    )

    return [
        CcInfo(compilation_context = cc_common.create_compilation_context(
            includes = depset([header.dirname]),
            headers = depset([header]),
            defines = depset(["RULE_NAME=\"{}\"".format(ctx.label.name)]),
        )),
        DefaultInfo(files = depset([header]), default_runfiles = ctx.runfiles(files = [hjson])),
        OutputGroupInfo(
            header = depset([header]),
        ),
    ]

autogen_cryptotest_header = rule(
    implementation = _cryptotest_header,
    attrs = {
        "deps": attr.label_list(allow_files = True),
        "template": attr.label(mandatory = True, allow_single_file = [".tpl"]),
        "hjson": attr.label(mandatory = True, allow_single_file = [".hjson"]),
        "test_setter": attr.label(
            allow_single_file = True,
            executable = True,
            mandatory = True,
            cfg = "exec",
        ),
    },
)
