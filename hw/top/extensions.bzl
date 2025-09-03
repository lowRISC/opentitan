# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def _top_desc_repo_impl(rctx):
    defs = """
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_modify_top")
"""
    nr_tops = len(rctx.attr.top_vars)
    for i in range(nr_tops):
        defs += "load(\"{}\", TOP{} = \"{}\")\n".format(str(rctx.attr.bazel_files[i]), i, rctx.attr.top_vars[i])

    defs += "\nALL_TOPS = [\n"
    for i in range(nr_tops):
        defs += "  opentitan_modify_top(TOP{}, name = \"{}\"),\n".format(i, rctx.attr.top_names[i])
    defs += "]\n"

    rctx.file("defs.bzl", defs)
    rctx.file("BUILD.bazel", "exports_files(glob([\"**\"]))\n")

top_desc_repo = repository_rule(
    implementation = _top_desc_repo_impl,
    doc = """
        Create a repository containing a `defs.bzl` file containing
        the description of all the tops, in the form of a single `ALL_TOPS`
        array whose elements are created by `opentitan_top`.
    """,
    # The attributes are directly forwarded from the `register` tag classes,
    # see documentation there.
    attrs = {
        "bazel_files": attr.label_list(),
        "top_vars": attr.string_list(),
        "top_names": attr.string_list(),
    },
)

_register = tag_class(
    attrs = {
        "bazel_file": attr.label(
            mandatory = True,
            allow_single_file = True,
            doc = "Bazel file containing the top description",
        ),
        "top_var": attr.string(
            mandatory = True,
            doc = "Name of the variable in the Bazel file containing the top description",
        ),
        "rename_top": attr.string(
            doc = "Optionally change the top name to avoid conflicts",
        ),
    },
    doc = """
Register a top with the build system. To do so, you must have a bazel file exporting
a variable containing the top description created by `opentitan_top`. For example,
Earlgrey's top description is located in hw/top_earlgrey/defs.bzl which exports
a variable named `EARLGREY`. In this case, you need to pass the label to the
`hw/top_earlgrey/defs.bzl` in `bazel_file` and `EARLGREY` in `top_var`.
""",
)

def _top_impl(ctx):
    reg_list = []
    expose_list = []
    for mod in ctx.modules:
        for reg in mod.tags.register:
            reg_list.append(reg)

    top_desc_repo(
        name = "tops_desc",
        bazel_files = [reg.bazel_file for reg in reg_list],
        top_vars = [reg.top_var for reg in reg_list],
        top_names = [reg.rename_top for reg in reg_list],
    )

top = module_extension(
    implementation = _top_impl,
    tag_classes = {
        "register": _register,
    },
    doc = """Extension to register tops with the build system.
The tops will be exposed in a repository called `tops_desc`. See `top_desc_repo`.""",
)
