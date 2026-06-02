# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:local.bzl", "local_repository")

def _extra_repo_impl(rctx):
    # This is basically a reimplementation of local_repository but doing
    # so avoids crafting paths manually in the extension which end up putting
    # absolute paths in the lock file. The issue fundamentally boils down to
    # the fact that when a repository extension executes, local_repository
    # treats path as relative to the *root* MODULE.bazel and not the extension's
    # MODULE.bazel
    src_dir = rctx.path(Label("@ot_provisioning_exts//:extra"))
    for p in src_dir.readdir():
        rctx.symlink(p, p.basename)

_extra_repo = repository_rule(
    implementation = _extra_repo_impl,
)

def _extra_impl(mctx):
    _extra_repo(name = "provisioning_exts_extra")

extra = module_extension(
    implementation = _extra_impl,
)
