# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Quality check rules for OpenTitan.
"""

load("@rules_cc//cc:action_names.bzl", "ACTION_NAMES", "C_COMPILE_ACTION_NAME")
load("@bazel_skylib//lib:shell.bzl", "shell")
load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load("//rules:rv.bzl", "rv_rule")

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

def _cc_aspect_impl(target, ctx, action_callback):
    """Aspect implementation for C/C++ targets with configurable callback."""

    def make_output_group_info(files = []):
        """Create an OutputGroupInfo with a name defined by `ctx`."""
        args = {ctx.attr._output_group_name: files}
        return OutputGroupInfo(**args)

    if ctx.rule.kind not in ["cc_library", "cc_binary", "cc_test"]:
        return [make_output_group_info()]

    if CcInfo in target:
        cc_info = target[CcInfo]
    elif hasattr(ctx.rule.attr, "deps"):
        # Some rules, like cc_binary, do NOT produce a CcInfo provider. Therefore,
        # we need to build one from its dependencies.
        cc_info = cc_common.merge_cc_infos(
            direct_cc_infos = [dep[CcInfo] for dep in ctx.rule.attr.deps if CcInfo in dep],
        )
    else:
        return [make_output_group_info()]
    cc_compile_ctx = cc_info.compilation_context

    cc_toolchain = find_cc_toolchain(ctx).cc
    feature_configuration = cc_common.configure_features(
        ctx = ctx,
        cc_toolchain = cc_toolchain,
        requested_features = ctx.features,
        unsupported_features = ctx.disabled_features,
    )

    if not hasattr(ctx.rule.attr, "srcs"):
        return [make_output_group_info()]
    all_srcs = []
    for src in ctx.rule.attr.srcs:
        all_srcs += [src for src in src.files.to_list() if src.is_source]

    outputs = []
    for src in all_srcs:
        if src.path.startswith("external/"):
            continue
        if not src.extension in ["c", "cc", "h"]:
            continue

        generated_file = ctx.actions.declare_file(
            "{}.{}.{}".format(src.basename, target.label.name, ctx.attr._output_file_suffix),
        )
        outputs.append(generated_file)

        opts = ctx.fragments.cpp.copts
        if hasattr(ctx.rule.attr, "copts"):
            opts += ctx.rule.attr.copts

        # TODO(dmcardle) What if an .h file should be compiled for C++? Perhaps
        # this should match the behavior in rules/cc_side_outputs.bzl.
        if src.extension in ["c", "h"]:
            opts += ctx.fragments.cpp.conlyopts
        else:
            opts += ctx.fragments.cpp.cxxopts
            if hasattr(ctx.rule.attr, "cxxopts"):
                opts += ctx.rule.attr.cxxopts

        c_compile_variables = cc_common.create_compile_variables(
            feature_configuration = feature_configuration,
            cc_toolchain = cc_toolchain,
            source_file = src.path,
            user_compile_flags = opts,
            include_directories = depset(
                direct = [src.dirname for src in cc_compile_ctx.headers.to_list()],
                transitive = [cc_compile_ctx.includes],
            ),
            quote_include_directories = cc_compile_ctx.quote_includes,
            system_include_directories = cc_compile_ctx.system_includes,
            framework_include_directories = cc_compile_ctx.framework_includes,
            preprocessor_defines = depset(
                direct = ctx.rule.attr.local_defines,
                transitive = [cc_compile_ctx.defines],
            ),
        )

        command_line = cc_common.get_memory_inefficient_command_line(
            feature_configuration = feature_configuration,
            action_name = ACTION_NAMES.c_compile,
            variables = c_compile_variables,
        )

        action_callback(ctx, cc_toolchain, cc_compile_ctx, generated_file, command_line, src)

    return [
        make_output_group_info(depset(direct = outputs)),
    ]

# To see which checks clang-tidy knows about, run this command:
#
#  ./bazelisk.sh run @lowrisc_rv32imcb_files//:bin/clang-tidy -- --checks='*' --list-checks
_CLANG_TIDY_CHECKS = [
    "clang-analyzer-core.*",
]

def _clang_tidy_run_action(ctx, cc_toolchain, cc_compile_ctx, generated_file, command_line, src):
    """Generates an action to run clang-tidy."""

    args = ctx.actions.args()

    # Add args that are consumed by the wrapper script.
    if ctx.attr._enable_fix:
        args.add("--ignore-clang-tidy-error")
    args.add(".clang-tidy.lock")
    args.add(generated_file)
    args.add_all(ctx.attr._clang_tidy.files)

    # Add args for clang-tidy.
    if len(_CLANG_TIDY_CHECKS) > 0:
        checks_pattern = ",".join(_CLANG_TIDY_CHECKS)
        args.add("--checks=" + checks_pattern)

        # Treat warnings from every enabled check as errors.
        args.add("--warnings-as-errors=" + checks_pattern)
    if ctx.attr._enable_fix:
        args.add("--fix")
        args.add("--fix-errors")

        # Use the nearest .clang_format file to format code adjacent to fixes.
        args.add("--format-style=file")

    # Specify a regex header filter. Without this, clang-tidy will not
    # report or fix errors in header files.
    args.add("--header-filter=.*\\.h$")
    args.add("--use-color")

    for arg in command_line:
        if arg in [src.path, "-fno-canonical-system-headers"]:
            continue
        args.add("--extra-arg=" + arg)

    # Tell clang-tidy which source file to analyze.
    args.add(src)

    ctx.actions.run(
        executable = ctx.attr._clang_tidy_wrapper.files_to_run,
        arguments = [args],
        inputs = depset(
            direct = [src],
            transitive = [
                cc_toolchain.all_files,
                cc_compile_ctx.headers,
            ],
        ),
        tools = [ctx.attr._clang_tidy.files_to_run],
        outputs = [generated_file],
        progress_message = "Running clang tidy on {}".format(src.path),
    )

def _make_clang_tidy_aspect(enable_fix):
    return aspect(
        implementation = lambda target, ctx: _cc_aspect_impl(target, ctx, _clang_tidy_run_action),
        attr_aspects = ["deps"],
        attrs = {
            "_clang_tidy_wrapper": attr.label(
                default = "//rules/scripts:clang_tidy.py",
                allow_single_file = True,
                cfg = "host",
                executable = True,
            ),
            "_clang_tidy": attr.label(
                default = "@lowrisc_rv32imcb_files//:bin/clang-tidy",
                allow_single_file = True,
                cfg = "host",
                executable = True,
                doc = "The clang-tidy executable",
            ),
            "_enable_fix": attr.bool(default = enable_fix),
            "_output_group_name": attr.string(default = "clang_tidy"),
            "_output_file_suffix": attr.string(default = "clang-tidy.out"),
        },
        incompatible_use_toolchain_transition = True,
        fragments = ["cpp"],
        host_fragments = ["cpp"],
        toolchains = ["@rules_cc//cc:toolchain_type"],
    )

clang_tidy_fix_aspect = _make_clang_tidy_aspect(True)
clang_tidy_check_aspect = _make_clang_tidy_aspect(False)

def _audit_sec_mmio_calls_run_action(ctx, cc_toolchain, cc_compile_ctx, generated_file, command_line, src):
    """Generates an action that runs the sec_mmio audit script on one source."""

    args = ctx.actions.args()
    args.add(generated_file)
    args.add(src)

    for arg in command_line:
        if arg in [src.path, "-fno-canonical-system-headers", "-c"]:
            continue
        elif arg.startswith("-march=rv32imc"):
            continue
        args.add(arg)

    ctx.actions.run(
        executable = ctx.attr._audit_tool.files_to_run,
        arguments = [args],
        inputs = depset(
            direct = [src],
            transitive = [
                cc_toolchain.all_files,
                cc_compile_ctx.headers,
            ],
        ),
        outputs = [generated_file],
    )

audit_sec_mmio_calls_aspect = aspect(
    implementation = lambda target, ctx: _cc_aspect_impl(target, ctx, _audit_sec_mmio_calls_run_action),
    attr_aspects = ["deps"],
    attrs = {
        "_audit_tool": attr.label(
            default = "//util/py/scripts:bazel_aspect_tool_audit_sec_mmio_calls",
            cfg = "host",
            executable = True,
        ),
        "_output_group_name": attr.string(default = "audit_sec_mmio"),
        "_output_file_suffix": attr.string(default = "clang-audit.out"),
    },
    incompatible_use_toolchain_transition = True,
    fragments = ["cpp"],
    host_fragments = ["cpp"],
    toolchains = ["@rules_cc//cc:toolchain_type"],
)

def _clang_tidy_test_impl(ctx):
    # Test rules must produce an exectuable, so create a dummy script. If the
    # clang-tidy rules were not test rules, the targets they instantiate could
    # not depend on test targets. For context, see issue #18726.
    out_file = ctx.actions.declare_file(ctx.label.name + ".dummy.bash")
    ctx.actions.write(out_file, "", is_executable = True)

    return [
        DefaultInfo(
            files = depset(
                transitive = [dep[OutputGroupInfo].clang_tidy for dep in ctx.attr.deps],
            ),
            executable = out_file,
        ),
    ]

clang_tidy_rv_test = rv_rule(
    implementation = _clang_tidy_test_impl,
    attrs = {
        "deps": attr.label_list(
            aspects = [clang_tidy_check_aspect],
        ),
    },
    test = True,
)

clang_tidy_test = rule(
    implementation = _clang_tidy_test_impl,
    attrs = {
        "deps": attr.label_list(
            aspects = [clang_tidy_check_aspect],
        ),
    },
    test = True,
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

def _modid_check_aspect_impl(target, ctx):
    """
    Verify that a binary (ELF file) does not contain conflicting module IDs
    using opentitantool. The result of this aspect is put is in modid_check
    output group.
    """

    # Make sure that the target is a binary, otherwise ignore it.
    if ctx.rule.kind != "cc_binary":
        return []

    # We create a file that will not contain anything: this is just to create a "link"
    # between the run action and the output group info. This way if we ask bazel for this
    # output group, it will automatically run the action. We could use a validation group
    # but at least this makes the check more explicit.
    generated_file = ctx.actions.declare_file("{}.mod-id".format(target.label.name))

    # Call "opentitantool status lint <files>"
    args = ctx.actions.args()
    args.add_all(["status", "lint", "--touch", generated_file])
    args.add_all(target.files)
    ctx.actions.run(
        executable = ctx.file._opentitantool,
        arguments = [args],
        inputs = target.files,
        tools = [],
        outputs = [generated_file],
        progress_message = "Checking module IDs for %{label}",
    )

    return [
        OutputGroupInfo(
            modid_check = depset(direct = [generated_file]),
        ),
    ]

modid_check_aspect = aspect(
    implementation = _modid_check_aspect_impl,
    attr_aspects = [],
    attrs = {
        # The rules to which we apply the aspect may not depend on opentitantool
        # so make sure that we depend on it. Make sure that it is built for the
        # execution platform since this aspect will be applied to targets built
        # for the OT platform.
        "_opentitantool": attr.label(
            default = "//sw/host/opentitantool",
            allow_single_file = True,
            executable = True,
            cfg = "exec",
        ),
    },
)

def _rustfmt_impl(ctx):
    # See rules/ujson.bzl
    rustfmt_files = ctx.attr._rustfmt.data_runfiles.files.to_list()
    rustfmt = [f for f in rustfmt_files if f.basename == "rustfmt"][0]

    out_file = ctx.actions.declare_file(ctx.label.name + ".bash")
    exclude_patterns = ["\\! -path {}".format(shell.quote(p)) for p in ctx.attr.exclude_patterns]
    include_patterns = ["-name {}".format(shell.quote(p)) for p in ctx.attr.patterns]
    workspace = ctx.file.workspace.path if ctx.file.workspace else ""
    substitutions = {
        "@@EXCLUDE_PATTERNS@@": " ".join(exclude_patterns),
        "@@INCLUDE_PATTERNS@@": " -o ".join(include_patterns),
        "@@RUSTFMT@@": shell.quote(rustfmt.short_path),
        "@@WORKSPACE@@": workspace,
    }
    ctx.actions.expand_template(
        template = ctx.file._runner,
        output = out_file,
        substitutions = substitutions,
        is_executable = True,
    )

    files = [rustfmt]
    if ctx.file.workspace:
        files.append(ctx.file.workspace)

    return DefaultInfo(
        runfiles = ctx.runfiles(files = files),
        executable = out_file,
    )

rustfmt_attrs = {
    "patterns": attr.string_list(
        default = ["*.rs"],
        doc = "Filename patterns for format checking",
    ),
    "exclude_patterns": attr.string_list(
        doc = "Filename patterns to exlucde from format checking",
    ),
    "workspace": attr.label(
        allow_single_file = True,
        doc = "Label of the WORKSPACE file",
    ),
    "_runner": attr.label(
        default = "//rules/scripts:rustfmt.template.sh",
        allow_single_file = True,
    ),
    "_rustfmt": attr.label(
        default = "@rules_rust//rust/toolchain:current_rustfmt_files",
        cfg = "exec",
    ),
}

rustfmt_fix = rule(
    implementation = _rustfmt_impl,
    attrs = rustfmt_attrs,
    executable = True,
)
