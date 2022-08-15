# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Quality check rules for OpenTitan.
"""

load("@bazel_skylib//lib:shell.bzl", "shell")

def _license_check_impl(ctx):
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
    implementation = _license_check_impl,
    attrs = {
        "config": attr.label(
            default = "//util:licence-checker.hjson",
            allow_single_file = True,
            doc = "Configuration file for the license checker",
        ),
        "license_check": attr.label(
            default = "//util:lowrisc_misc-linters/licence-checker/licence-checker.py",
            allow_single_file = True,
            cfg = "host",
            executable = True,
            doc = "The license checker executable",
        ),
        "_runner": attr.label(
            default = "//rules/scripts:license_check.template.sh",
            allow_single_file = True,
        ),
    },
    executable = True,
)

def _clang_format_impl(ctx):
    out_file = ctx.actions.declare_file(ctx.label.name + ".bash")
    exclude_patterns = ["\\! -path {}".format(shell.quote(p)) for p in ctx.attr.exclude_patterns]
    include_patterns = ["-name {}".format(shell.quote(p)) for p in ctx.attr.patterns]
    substitutions = {
        "@@EXCLUDE_PATTERNS@@": " ".join(exclude_patterns),
        "@@INCLUDE_PATTERNS@@": " -o ".join(include_patterns),
        "@@CLANG_FORMAT@@": shell.quote(ctx.executable.clang_format.short_path),
        "@@DIFF_COMMAND@@": shell.quote(ctx.attr.diff_command),
        "@@MODE@@": shell.quote(ctx.attr.mode),
    }
    ctx.actions.expand_template(
        template = ctx.file._runner,
        output = out_file,
        substitutions = substitutions,
        is_executable = True,
    )

    return DefaultInfo(
        files = depset([out_file]),
        runfiles = ctx.runfiles(files = [ctx.executable.clang_format]),
        executable = out_file,
    )

clang_format_check = rule(
    implementation = _clang_format_impl,
    attrs = {
        "patterns": attr.string_list(
            default = ["*.c", "*.h", "*.cc", "*.cpp"],
            doc = "Filename patterns for format checking",
        ),
        "exclude_patterns": attr.string_list(
            doc = "Filename patterns to exlucde from format checking",
        ),
        "mode": attr.string(
            default = "diff",
            values = ["diff", "fix"],
            doc = "Execution mode: display diffs or fix formatting",
        ),
        "diff_command": attr.string(
            default = "diff -u",
            doc = "Command to execute to display diffs",
        ),
        "clang_format": attr.label(
            default = "@com_lowrisc_toolchain_rv32imc_compiler//:bin/clang-format",
            allow_single_file = True,
            cfg = "host",
            executable = True,
            doc = "The clang-format executable",
        ),
        "_runner": attr.label(
            default = "//rules/scripts:clang_format.template.sh",
            allow_single_file = True,
        ),
    },
    executable = True,
)

def _html_coverage_report_impl(ctx):
    out_file = ctx.actions.declare_file(ctx.label.name + ".bash")
    substitutions = {}
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

html_coverage_report = rule(
    implementation = _html_coverage_report_impl,
    attrs = {
        "_runner": attr.label(
            default = "//rules/scripts:html_coverage_report.template.sh",
            allow_single_file = True,
        ),
    },
    executable = True,
)
