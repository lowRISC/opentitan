# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

_HOOKS_TEMPLATE = """
def hooks_repo(name):
    native.local_repository(
        name = name,
        path = "{hooks_dir}",
    )
"""

_SECURE_HOOKS_TEMPLATE = """
def secure_hooks_repo(name):
    native.local_repository(
        name = name,
        path = "{hooks_dir}",
    )
"""

_PERSO_EXTS_TEMPLATE = """
def perso_exts_repo(name):
    native.local_repository(
        name = name,
        path = "{perso_exts_dir}",
    )
"""

_BUILD = """
exports_files(glob(["**"]))
"""

def _hooks_setup_impl(rctx):
    hooks_dir = rctx.os.environ.get("MANUFACTURER_HOOKS_DIR", rctx.attr.dummy)
    rctx.file("repos.bzl", _HOOKS_TEMPLATE.format(hooks_dir = hooks_dir))
    rctx.file("BUILD.bazel", _BUILD)

hooks_setup = repository_rule(
    implementation = _hooks_setup_impl,
    attrs = {
        "dummy": attr.string(
            mandatory = True,
            doc = "Location of the dummy hooks directory.",
        ),
    },
    environ = ["MANUFACTURER_HOOKS_DIR"],
)

def _secure_hooks_setup_impl(rctx):
    secure_hooks_dir = rctx.os.environ.get("SECURE_MANUFACTURER_HOOKS_DIR", rctx.attr.dummy)
    rctx.file("repos.bzl", _SECURE_HOOKS_TEMPLATE.format(hooks_dir = secure_hooks_dir))
    rctx.file("BUILD.bazel", _BUILD)

secure_hooks_setup = repository_rule(
    implementation = _secure_hooks_setup_impl,
    attrs = {
        "dummy": attr.string(
            mandatory = True,
            doc = "Location of the dummy hooks directory.",
        ),
    },
    environ = ["SECURE_MANUFACTURER_HOOKS_DIR"],
)

def _perso_exts_setup_impl(rctx):
    perso_exts_dir = rctx.os.environ.get("PERSO_EXTS_DIR", rctx.attr.dummy)
    rctx.file("repos.bzl", _PERSO_EXTS_TEMPLATE.format(perso_exts_dir = perso_exts_dir))
    rctx.file("BUILD.bazel", _BUILD)

perso_exts_setup = repository_rule(
    implementation = _perso_exts_setup_impl,
    attrs = {
        "dummy": attr.string(
            mandatory = True,
            doc = "Location of the dummy personalization FW extensions directory.",
        ),
    },
    environ = ["PERSO_EXTS_DIR"],
)
