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

_PROV_EXTS_TEMPLATE = """
def provisioning_exts_repo(name):
    native.local_repository(
        name = name,
        path = "{provisioning_exts_dir}",
    )
"""

_ROM_HOOKS_TEMPLATE = """
def rom_hooks_repo(name):
    native.local_repository(
        name = name,
        path = "{hooks_dir}",
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

def _provisioning_exts_setup_impl(rctx):
    provisioning_exts_dir = rctx.os.environ.get("PROV_EXTS_DIR", rctx.attr.dummy)
    rctx.file("repos.bzl", _PROV_EXTS_TEMPLATE.format(provisioning_exts_dir = provisioning_exts_dir))
    rctx.file("BUILD.bazel", _BUILD)

provisioning_exts_setup = repository_rule(
    implementation = _provisioning_exts_setup_impl,
    attrs = {
        "dummy": attr.string(
            mandatory = True,
            doc = "Location of the dummy provisioning extensions directory.",
        ),
    },
    environ = ["PROV_EXTS_DIR"],
)

def _rom_hooks_setup_impl(rctx):
    rom_hooks_dir = rctx.os.environ.get("ROM_HOOKS_DIR", rctx.attr.dummy)
    rctx.file("repos.bzl", _ROM_HOOKS_TEMPLATE.format(hooks_dir = rom_hooks_dir))
    rctx.file("BUILD.bazel", _BUILD)

rom_hooks_setup = repository_rule(
    implementation = _rom_hooks_setup_impl,
    attrs = {
        "dummy": attr.string(
            mandatory = True,
            doc = "Location of the dummy ROM extensions directory.",
        ),
    },
    environ = ["ROM_HOOKS_DIR"],
)
