# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:local.bzl", "local_repository")

def _hooks_impl(rctx):
    for mod in rctx.modules:
        for repo in mod.tags.repo:
            dir = rctx.getenv(repo.env, repo.dummy)
            local_repository(name = repo.name, path = dir)

_repo_class = tag_class(
    attrs = {
        "name": attr.string(mandatory = True),
        "env": attr.string(mandatory = True),
        "dummy": attr.string(mandatory = True),
    },
)

hooks = module_extension(
    implementation = _hooks_impl,
    tag_classes = {"repo": _repo_class},
)
