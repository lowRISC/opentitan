# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Quality check rules for OpenTitan.
"""

load("@bazel_skylib//lib:shell.bzl", "shell")

def _ensure_tag(tags, *tag):
    for t in tag:
        if t not in tags:
            tags.append(t)
    return tags

def _clang_format_impl(ctx):
    out_file = ctx.actions.declare_file(ctx.label.name + ".bash")
    exclude_patterns = ["\\! -path {}".format(shell.quote(p)) for p in ctx.attr.exclude_patterns]
    include_patterns = ["-name {}".format(shell.quote(p)) for p in ctx.attr.patterns]
    workspace = ctx.file.workspace.path if ctx.file.workspace else ""
    substitutions = {
        "@@EXCLUDE_PATTERNS@@": " ".join(exclude_patterns),
        "@@INCLUDE_PATTERNS@@": " -o ".join(include_patterns),
        "@@CLANG_FORMAT@@": shell.quote(ctx.executable.clang_format.short_path),
        "@@DIFF_COMMAND@@": shell.quote(ctx.attr.diff_command),
        "@@MODE@@": shell.quote(ctx.attr.mode),
        "@@WORKSPACE@@": workspace,
    }
    ctx.actions.expand_template(
        template = ctx.file._runner,
        output = out_file,
        substitutions = substitutions,
        is_executable = True,
    )

    files = [ctx.executable.clang_format]
    if ctx.file.workspace:
        files.append(ctx.file.workspace)

    return DefaultInfo(
        runfiles = ctx.runfiles(files = files),
        executable = out_file,
    )

clang_format_attrs = {
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
        default = "@lowrisc_rv32imcb_files//:bin/clang-format",
        allow_single_file = True,
        cfg = "host",
        executable = True,
        doc = "The clang-format executable",
    ),
    "workspace": attr.label(
        allow_single_file = True,
        doc = "Label of the WORKSPACE file",
    ),
    "_runner": attr.label(
        default = "//rules/scripts:clang_format.template.sh",
        allow_single_file = True,
    ),
}

clang_format_check = rule(
    implementation = _clang_format_impl,
    attrs = clang_format_attrs,
    executable = True,
)

_clang_format_test = rule(
    implementation = _clang_format_impl,
    attrs = clang_format_attrs,
    test = True,
)

def clang_format_test(**kwargs):
    tags = kwargs.get("tags", [])

    # Note: the "external" tag is a workaround for bazelbuild#15516.
    kwargs["tags"] = _ensure_tag(tags, "no-sandbox", "no-cache", "external")
    _clang_format_test(**kwargs)

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
