# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rust `cargo` related rules for OpenTitan.
"""

def _cargo_raze_impl(ctx):
    out_file = ctx.actions.declare_file(ctx.label.name + ".bash")
    substitutions = {
        "@@FILES@@": " ".join(ctx.attr.cargo),
        "@@CARGO_RAZE@@": ctx.attr.cargo_raze,
    }
    ctx.actions.expand_template(
        template = ctx.file._runner,
        output = out_file,
        substitutions = substitutions,
        is_executable = True,
    )
    return DefaultInfo(
        files = depset([out_file]),
        executable = out_file,
    )

cargo_raze = rule(
    implementation = _cargo_raze_impl,
    attrs = {
        # This should really be a label_list, but cargo-raze generates a
        # BUILD file in the same directory as Cargo.toml and prevents us
        # from making Cargo.toml visible to bazel.
        "cargo": attr.string_list(
            doc = "Workspace relative paths of Cargo.toml files",
        ),
        # This should also be a label, but we need to pass the raw text
        # of the label into the template script.
        "cargo_raze": attr.string(
            default = "@cargo_raze//:raze",
            doc = "Label of cargo-raze",
        ),
        "_runner": attr.label(
            default = "//rules/scripts:cargo_raze.template.sh",
            allow_single_file = True,
        ),
    },
    executable = True,
)
