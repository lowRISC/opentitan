# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:local.bzl", "local_repository")

def _copy_from_label_impl(rctx):
    src_dir = rctx.path(rctx.attr.src)
    for p in src_dir.readdir():
        contents = rctx.read(p)
        rel_path = str(p)[len(str(src_dir)):].lstrip("/")
        rctx.file(rel_path, contents)


copy_from_label = repository_rule(
    implementation = _copy_from_label_impl,
    attrs = {
        "src": attr.label(),
    }
)

def _hooks_impl(rctx):
    for mod in rctx.modules:
        for repo in mod.tags.repo:
            d = rctx.getenv(repo.env)
            if d:
                local_repository(name = repo.name, path = d)
            else:
                copy_from_label(name = repo.name, src = repo.dummy)

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
