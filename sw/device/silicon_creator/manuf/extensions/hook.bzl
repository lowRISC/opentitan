# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def _hook_impl(rctx):
    # This is basically a reimplementation of local_repository
    src_dir = rctx.path(Label("@ot_provisioning_exts//:repo"))
    for p in src_dir.readdir():
        rctx.symlink(p, p.basename)

hook = repository_rule(
    implementation = _hook_impl,
)
