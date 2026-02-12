# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:local.bzl", "local_repository")

def _symlink_from_label_impl(rctx):
    src_dir = rctx.path(rctx.attr.src)
    for p in src_dir.readdir():
        rctx.symlink(p, p.basename)

symlink_from_label = repository_rule(
    implementation = _symlink_from_label_impl,
    attrs = {
        "src": attr.label(),
    },
    doc = "Create a repository that is a symlinked to a subdirectory in the project.  This is used to create hooks repos that can be overriden with an environment variable.",
)

def _hooks_impl(rctx):
    for mod in rctx.modules:
        for repo in mod.tags.repo:
            d = rctx.getenv(repo.env)
            if d:
                local_repository(name = repo.name, path = d)
            else:
                symlink_from_label(name = repo.name, src = repo.dummy)

_repo_class = tag_class(
    attrs = {
        "name": attr.string(mandatory = True),
        "env": attr.string(mandatory = True),
        "dummy": attr.label(mandatory = True),
    },
)

hooks = module_extension(
    implementation = _hooks_impl,
    tag_classes = {"repo": _repo_class},
)
