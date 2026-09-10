# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def _exclude_files_impl(ctx):
    out = []
    for src in ctx.files.srcs:
        include = True
        for suffix in ctx.attr.exclude_suffix:
            if src.path.endswith(suffix):
                include = False
                break
        if include:
            out.append(src)
    return [DefaultInfo(files = depset(out))]

exclude_files = rule(
    implementation = _exclude_files_impl,
    attrs = {
        "srcs": attr.label_list(
            allow_files = True,
            mandatory = True,
            doc = "Targets producing file outputs",
        ),
        "exclude_suffix": attr.string_list(
            doc = "File suffixes to exclude from the result",
        ),
    },
)

def _output_groups(ctx):
    out = []
    for src in ctx.attr.srcs:
        src = src[OutputGroupInfo]
        for group in ctx.attr.groups:
            out.append(src[group])
    return DefaultInfo(
        files = depset(transitive = out),
    )

output_groups = rule(
    implementation = _output_groups,
    attrs = {
        "srcs": attr.label_list(
            mandatory = True,
            providers = [OutputGroupInfo],
            doc = "Targets producing file outputs",
        ),
        "groups": attr.string_list(
            doc = "Output groups to collect from the srcs",
        ),
    },
)

def _matches_filter(val, filt):
    if not filt:
        return True
    for f in filt:
        if f in val:
            return True
    return False

def _copy_files(ctx):
    files = []
    for file in ctx.files.srcs:
        if _matches_filter(file.basename, ctx.attr.filter):
            files.append(file)

    out_file = ctx.actions.declare_file(ctx.label.name + ".bash")
    substitutions = {
        # This is maybe a bit naughty: we rely on the fact that the `package`
        # portion of the `relative_to` label looks just like the dirname
        # of the file and the package is relative to the root of the
        # workspace in which the rule resides.
        "__DEST__": ctx.attr.relative_to.label.package,
        "__FILES__": " ".join([f.path for f in files]),
        "__WORKSPACE__": ctx.attr.workspace_env,
    }
    ctx.actions.expand_template(
        template = ctx.file._runner,
        output = out_file,
        substitutions = substitutions,
        is_executable = True,
    )

    return [DefaultInfo(
        runfiles = ctx.runfiles(files = files),
        executable = out_file,
    )]

copy_files = rule(
    implementation = _copy_files,
    attrs = {
        "srcs": attr.label_list(
            mandatory = True,
            allow_files = True,
            doc = "Targets producing file outputs",
        ),
        "relative_to": attr.label(
            mandatory = True,
            allow_single_file = True,
            doc = "Label of a file in the same subdir that the files should be copied to.",
        ),
        "filter": attr.string_list(
            default = [],
            doc = "Substrings that must match the filename to qualify the file for copying.  The rule will copy files if any one of the substrings matches.",
        ),
        "workspace_env": attr.string(
            default = "BUILD_WORKSPACE_DIRECTORY",
            doc = "An environment variable that holds the path to the root of the workspace.",
        ),
        "_runner": attr.label(
            default = "//rules/scripts:copy_files.template.sh",
            allow_single_file = True,
        ),
    },
    executable = True,
)

def _hash_file_map_fname(file):
    # We produce the format expected by the hashing script, using the short path as the
    # hashed file to avoid depending on the bazel configuration.
    return file.path + "@" + file.short_path

def _hash_files(ctx):
    inputs = ctx.files.src
    if ctx.attr.output_group:
        inputs = getattr(ctx.attr.src[OutputGroupInfo], ctx.attr.output_group).to_list()

    list_file = ctx.actions.declare_file(ctx.label.name + ".list")
    hash_file = ctx.actions.declare_file(ctx.label.name + ".hash")

    args = ctx.actions.args()

    # This will automatically recursively expand directories which in particular handles
    # all the complexity of the various bazel symlinks.
    args.add_all(
        inputs,
        map_each = _hash_file_map_fname,
        expand_directories = True,
    )

    # If the command line becomes too big, spill to a file.
    args.use_param_file("--file-list=%s")

    ctx.actions.run(
        inputs = inputs,
        outputs = [hash_file, list_file],
        executable = ctx.executable._hash_files,
        arguments = [
            "--output-list",
            list_file.path,
            "--output-hash",
            hash_file.path,
            args,
        ],
    )

    return [
        DefaultInfo(files = depset([hash_file])),
        OutputGroupInfo(list = depset([list_file])),
    ]

hash_files = rule(
    implementation = _hash_files,
    doc = """Hash the content of the file and produce a file containing that hash.
        If the src is a directory, its content will be hashed recursively.""",
    attrs = {
        "src": attr.label(
            mandatory = True,
            allow_files = True,
            doc = "Target producing file outputs",
        ),
        "output_group": attr.string(
            doc = "Output group to use (optional)",
        ),
        "_hash_files": attr.label(
            default = "//rules/scripts:hash_files",
            cfg = "exec",
            executable = True,
        ),
    },
)
