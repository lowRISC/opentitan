# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@bazel_skylib//lib:paths.bzl", "paths")
load("//rules:rv.bzl", "rv_rule")
load("//rules/opentitan:toolchain.bzl", "LOCALTOOLS_TOOLCHAIN")

def _certificate_codegen_impl(ctx):
    tc = ctx.toolchains[LOCALTOOLS_TOOLCHAIN]

    basename = paths.replace_extension(ctx.file.template.path, "")

    out_c = ctx.actions.declare_file("{}.c".format(basename))
    out_h = ctx.actions.declare_file("{}.h".format(basename))
    outputs = [out_c, out_h]
    ctx.actions.run(
        outputs = outputs,
        inputs = [
            ctx.file.template,
        ],
        arguments = [
            "--rcfile=",
            "--quiet",
            "certificate",
            "codegen",
            "--template={}".format(ctx.file.template.path),
            "--output-c={}".format(out_c.path),
            "--output-h={}".format(out_h.path),
        ],
        executable = tc.tools.opentitantool,
        mnemonic = "GenCertTemplate",
    )
    return [
        DefaultInfo(files = depset(outputs)),
        OutputGroupInfo(
            sources = depset([out_c]),
            headers = depset([out_h]),
        ),
    ]

# TODO: document
certificate_codegen = rv_rule(
    implementation = _certificate_codegen_impl,
    attrs = {
        "template": attr.label(allow_single_file = True, doc = "path to the hjson template file"),
    },
    toolchains = [LOCALTOOLS_TOOLCHAIN],
)

# TODO: document
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
