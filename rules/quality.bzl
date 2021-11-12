# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Quality check rules for OpenTitan.
"""

load("@bazel_skylib//lib:shell.bzl", "shell")

def _license_test_impl(ctx):
    args = [
        "--config={}".format(ctx.file.config.path),
        ".",
    ]

    out_file = ctx.actions.declare_file(ctx.label.name + ".bash")
    substitutions = {
        "@@ARGS@@": shell.array_literal(args),
        "@@LICENSE_CHECK@@": shell.quote(ctx.executable.license_check.short_path),
    }
    ctx.actions.expand_template(
        template = ctx.file._runner,
        output = out_file,
        substitutions = substitutions,
        is_executable = True,
    )

    return DefaultInfo(
        files = depset([out_file]),
        runfiles = ctx.runfiles(files = [ctx.executable.license_check]),
        executable = out_file,
    )

license_check = rule(
    implementation = _license_test_impl,
    attrs = {
        "config": attr.label(
            default = "//util:licence-checker.hjson",
            allow_single_file = True,
            doc = "Configuration file for the license checker",
        ),
        "license_check": attr.label(
            default = "//util/lowrisc_misc-linters/licence-checker:licence-checker.py",
            allow_single_file = True,
            cfg = "host",
            executable = True,
            doc = "The license checker executable",
        ),
        "_runner": attr.label(
            default = "//rules/scripts:license_check.bash.template",
            allow_single_file = True,
        ),
    },
    executable = True,
)
