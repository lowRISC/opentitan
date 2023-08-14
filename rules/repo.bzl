# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@python3//:defs.bzl", "interpreter")
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
load("@bazel_skylib//lib:paths.bzl", "paths")

def http_archive_or_local(local = None, **kwargs):
    if not local:
        http_archive(**kwargs)
    elif ("build_file" in kwargs or
          "build_file_content" in kwargs or
          "workspace_file" in kwargs or
          "workspace_file_content" in kwargs):
        native.new_local_repository(
            name = kwargs.get("name"),
            path = local,
            build_file = kwargs.get("build_file"),
            build_file_content = kwargs.get("build_file_content"),
            workspace_file = kwargs.get("workspace_file"),
            workspace_file_content = kwargs.get("workspace_file_content"),
        )
    else:
        native.local_repository(
            name = kwargs.get("name"),
            path = local,
        )

def _bare_repository_impl(rctx):
    if rctx.attr.local:
        workspace_root = str(rctx.path(rctx.attr.workspace).dirname.realpath)
        result = rctx.execute(
            [
                rctx.path(rctx.attr.python_interpreter),
                rctx.attr._symlink_tree,
                paths.join(workspace_root, rctx.attr.local),
                ".",
            ],
            quiet = False,
        )
        if result.return_code != 0:
            fail("Error initializing repo for {}".format(rctx.attr.local))
    elif rctx.attr.url:
        rctx.download_and_extract(
            url = rctx.attr.url,
            sha256 = rctx.attr.sha256,
            stripPrefix = rctx.attr.strip_prefix,
        )
    else:
        fail("Specify a `url` or `local` path")

    for rpath, lpath in rctx.attr.additional_files.items():
        rctx.symlink(rctx.path(lpath), rpath)
    for rpath, content in rctx.attr.additional_files_content.items():
        rctx.file(rpath, content)

bare_repository = repository_rule(
    implementation = _bare_repository_impl,
    attrs = {
        "url": attr.string(doc = "Location of an archive file (exclusive with `local`)."),
        "sha256": attr.string(doc = "SHA256 of the archive."),
        "strip_prefix": attr.string(doc = "Prefix to strip when extracting the archive."),
        "local": attr.string(doc = "Path to a local subdirectory (exclusive with `url`)."),
        "additional_files": attr.string_dict(
            doc = "Additional files to place in the repository (mapping repo filename to local file).",
        ),
        "additional_files_content": attr.string_dict(
            doc = "Additional files to place in the repository (mapping repo filename to strings).",
        ),
        "python_interpreter": attr.label(
            default = interpreter,
            allow_single_file = True,
            doc = "Python interpreter to use.",
        ),
        "_symlink_tree": attr.label(
            default = Label("//rules/scripts:symlink_tree.py"),
            allow_files = True,
            doc = "Script to create symlink trees for the `local` case.",
        ),
        "workspace": attr.label(
            default = Label("//:WORKSPACE"),
            allow_single_file = True,
            doc = "Root workspace.",
        ),
    },
    doc = """
        A bare_repository is a repo that needs additional files (such as a BUILD hierarchy)
        added to it.  This is similar to adding a `build_file` to an `http_repository` or
        `new_local_repository` rule, except that multiple files may be added.
    """,
)
