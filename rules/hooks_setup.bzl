# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

_TEMPLATE = """
def hooks_repo(name):
    native.local_repository(
        name = name,
        path = "{hooks_dir}",
    )
"""

_BUILD = """
exports_files(glob(["**"]))
"""

def _hooks_setup_impl(rctx):
    hooks_dir = rctx.os.environ.get("CLOSED_SOURCE_HOOKS", rctx.attr.dummy)
    rctx.file("repos.bzl", _TEMPLATE.format(hooks_dir = hooks_dir))
    rctx.file("BUILD.bazel", _BUILD)

hooks_setup = repository_rule(
    implementation = _hooks_setup_impl,
    attrs = {
        "dummy": attr.string(
            mandatory = True,
            doc = "Location of the dummy hooks directory.",
        ),
    },
    environ = ["CLOSED_SOURCE_HOOKS"],
)
