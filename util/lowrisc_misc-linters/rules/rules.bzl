# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Bazel rules for lowRISC linters."""

load("@bazel_skylib//lib:shell.bzl", "shell")
load("@lowrisc_misc_linters_pip//:requirements.bzl", "entry_point")

def _licence_check_impl(ctx):
    config = ctx.file.config
    if not config:
        config = ctx.actions.declare_file(ctx.label.name + ".hjson")
        ctx.actions.expand_template(
            template = ctx.file._config,
            output = config,
            substitutions = {
                "@@LICENCE@@": "'''" + ctx.attr.licence + "'''",
                "@@MATCH_REGEX@@": "true" if ctx.attr.match_regex else "false",
                "@@EXCLUDE_PATHS@@": ', '.join(['"{}"'.format(pat) for pat in ctx.attr.exclude_patterns]),
            },
        )

    # Hack to make Bazel build the checker correctly.
    #
    # Bazel py_binaries require a .runfiles directory to be present, but for
    # some reason or another it does not provide a good way to extract those
    # for building as a dependency from a PyInfo provider.
    #
    # https://github.com/bazelbuild/bazel/issues/7357
    checker = ctx.actions.declare_file(ctx.label.name + ".checker-witness")
    ctx.actions.run_shell(
        tools = [ctx.executable.licence_check],
        outputs = [checker],
        command = 'touch "{}"'.format(checker.path),
    )

    script = ctx.actions.declare_file(ctx.label.name + ".bash")
    ctx.actions.expand_template(
        template = ctx.file._runner,
        output = script,
        substitutions = {
            "@@LICENCE_CHECKER@@": ctx.executable.licence_check.path,
            "@@CONFIG@@": config.path,
        },
        is_executable = True,
    )

    runfiles = ctx.runfiles(files = [config, checker], transitive_files = ctx.attr.licence_check.files)
    runfiles = runfiles.merge(
      ctx.attr.licence_check.default_runfiles,
    )

    return DefaultInfo(
        runfiles = runfiles,
        executable = script,
    )

licence_check = rule(
    implementation = _licence_check_impl,
    attrs = {
        "config": attr.label(
            allow_single_file = True,
            doc = "HJSON configuration file override for the licence checker",
        ),
        "licence": attr.string(
            mandatory = True,
            doc = "Text of the licence header to use",
        ),
        "match_regex": attr.bool(
            default = False,
            doc = "Whether to use regex-matching for the licence text",
        ),
        "exclude_patterns": attr.string_list(
            default = [],
            doc = "File patterns to exclude from licence enforcement",
        ),
        "licence_check": attr.label(
            default = "//licence-checker",
            cfg = "host",
            executable = True,
            doc = "The licence checker executable",
        ),
        "_runner": attr.label(
            default = "//rules:licence-checker-runner.template.sh",
            allow_single_file = True,
        ),
        "_config": attr.label(
            default = "//rules:licence-checker-config.template.hjson",
            allow_single_file = True,
        ),
        "_sh_runfiles": attr.label(
            default = "@bazel_tools//tools/bash/runfiles",
            allow_single_file = True,
        ),
    },
    executable = True,
)

def _yapf_check_impl(ctx):
    # Hack to make Bazel build the checker correctly.
    #
    # Bazel py_binaries require a .runfiles directory to be present, but for
    # some reason or another it does not provide a good way to extract those
    # for building as a dependency from a PyInfo provider.
    #
    # https://github.com/bazelbuild/bazel/issues/7357
    checker = ctx.actions.declare_file(ctx.label.name + ".yapf")
    ctx.actions.run_shell(
        tools = [ctx.executable.yapf],
        outputs = [checker],
        command = 'touch "{}"'.format(checker.path),
    )

    script = ctx.actions.declare_file(ctx.label.name + ".bash")
    exclude_patterns = ["\\! -path {}".format(shell.quote(p)) for p in ctx.attr.exclude_patterns]
    include_patterns = ["-name {}".format(shell.quote(p)) for p in ctx.attr.patterns]
    ctx.actions.expand_template(
        template = ctx.file._runner,
        output = script,
        substitutions = {
            "@@YAPF@@": ctx.executable.yapf.path,
            "@@EXCLUDE_PATTERNS@@": " ".join(exclude_patterns),
            "@@INCLUDE_PATTERNS@@": " -o ".join(include_patterns),
            "@@STYLE@@": ctx.file.style.path,
            "@@MODE@@": ctx.attr.mode,
        },
        is_executable = True,
    )

    runfiles = ctx.runfiles(
        files = [ctx.file.style, checker],
        transitive_files = ctx.attr.yapf.files,
    )
    runfiles = runfiles.merge(
        ctx.attr.yapf.default_runfiles,
    )

    return DefaultInfo(
        runfiles = runfiles,
        executable = script,
    )

yapf_check = rule(
    implementation = _yapf_check_impl,
    attrs = {
        "patterns": attr.string_list(
            default = ["*.py"],
            doc = "Filename patterns for format checking",
        ),
        "exclude_patterns": attr.string_list(
            doc = "Filename patterns to exlucde from format checking",
        ),
        "style": attr.label(
            default = "//:.style.yapf",
            allow_single_file = True,
            doc = ".style.yapf configuration file",
        ),
        "mode": attr.string(
            mandatory = True,
            doc = "The mode to run yapf in",
        ),
        "yapf": attr.label(
            default = entry_point("yapf"),
            cfg = "host",
            executable = True,
            doc = "The yapf executable",
        ),
        "_runner": attr.label(
            default = "//rules:yapf-runner.template.sh",
            allow_single_file = True,
        ),
    },
    executable = True,
)

