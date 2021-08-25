# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Autogeneration rules for OpenTitan.

The rules in this file are for autogenerating various file resources
used by the OpenTitan build, such as register definition files generated
from hjson register descriptions.
"""

def _autogen_hjson_header(ctx):
    header = ctx.actions.declare_file("{}.h".format(ctx.label.name))
    ctx.actions.run(
        outputs = [header],
        inputs = ctx.files.srcs + ctx.files._tool,
        arguments = [
            "-D",
            "-o",
            header.path,
        ] + [src.path for src in ctx.files.srcs],
        executable = ctx.files._tool[0],
    )
    return [CcInfo(compilation_context = cc_common.create_compilation_context(
        includes = depset([header.dirname]),
        headers = depset([header]),
    ))]

autogen_hjson_header = rule(
    implementation = _autogen_hjson_header,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "_tool": attr.label(default = "//util:regtool.py", allow_files = True),
    },
)
