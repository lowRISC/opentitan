# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@bazel_skylib//lib:paths.bzl", "paths")
load("//rules:rv.bzl", "rv_rule")
load("//rules/opentitan:toolchain.bzl", "LOCALTOOLS_TOOLCHAIN")

def _certificate_codegen_impl(ctx):
    tc = ctx.toolchains[LOCALTOOLS_TOOLCHAIN]

    basename = paths.replace_extension(ctx.file.template.path, "")

    # Output files before formatting.
    pre_c = ctx.actions.declare_file("{}.pre.c".format(basename))
    pre_h = ctx.actions.declare_file("{}.pre.h".format(basename))

    # Final output files.
    out_c = ctx.actions.declare_file("{}.c".format(basename))
    out_h = ctx.actions.declare_file("{}.h".format(basename))
    ctx.actions.run(
        outputs = [pre_c, pre_h],
        inputs = [
            ctx.file.template,
        ],
        arguments = [
            "--rcfile=",
            "--quiet",
            "certificate",
            "codegen",
            "--template={}".format(ctx.file.template.path),
            "--output-c={}".format(pre_c.path),
            "--output-h={}".format(pre_h.path),
        ],
        executable = tc.tools.opentitantool,
        mnemonic = "GenCertTemplate",
    )

    # Format files
    format_list = {out_c: pre_c, out_h: pre_h}
    for (out, pre) in format_list.items():
        ctx.actions.run_shell(
            outputs = [out],
            inputs = [pre, ctx.executable.clang_format],
            command = "{} {} > {}".format(ctx.executable.clang_format.path, pre.path, out.path),
            mnemonic = "ClangFormat",
        )

    return [
        DefaultInfo(files = depset([out_c, out_h])),
        OutputGroupInfo(
            sources = depset([out_c]),
            headers = depset([out_h]),
        ),
    ]

# This rule uses `opentitantool certificate codegen` to generate the
# source files of the C certificate generator. Those source files
# need to be compiled and linked with the asn1 library: this is NOT
# done by this rule. The generated files are put in the following
# output groups:
# - "sources": contains the implementation of the generator.
# - "headers": contains the header containing the definitions and declaration.
# All files produced by this rule will be formatted by clang-format.
certificate_codegen = rv_rule(
    implementation = _certificate_codegen_impl,
    attrs = {
        "template": attr.label(allow_single_file = True, doc = "path to the hjson template file"),
        "clang_format": attr.label(
            default = "@lowrisc_rv32imcb_files//:bin/clang-format",
            allow_single_file = True,
            cfg = "host",
            executable = True,
            doc = "The clang-format executable",
        ),
    },
    toolchains = [LOCALTOOLS_TOOLCHAIN],
)

# This macro leverages the `certificate_codegen` rule to
# generate the C code of a certificate generator. It creates
# the following targets:
# - <name>: output of `certificate_codegen`
# - <name>_srcs: filegroup corresponding to the `sources` output group of <name>
# - <name>_hdrs: filegroup corresponding to the `headers` output group of <name>
# - <name>_library: cc_library that compiles the sources, exports the headers and links to the asn1
#   library.
def certificate_template(name, template):
    certificate_codegen(
        name = name,
        template = template,
    )

    native.filegroup(
        name = "{}_srcs".format(name),
        srcs = [":{}".format(name)],
        output_group = "sources",
    )
    native.filegroup(
        name = "{}_hdrs".format(name),
        srcs = [":{}".format(name)],
        output_group = "headers",
    )

    native.cc_library(
        name = "{}_library".format(name),
        srcs = [":{}_srcs".format(name)],
        hdrs = [":{}_hdrs".format(name)],
        deps = [
            ":asn1",
        ],
    )
