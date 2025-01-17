# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

NONHERMETIC_ENV_VARS = [
    "PATH",
    "XILINX_VIVADO",
    "XILINXD_LICENSE_FILE",
]

def _nonhermetic_repo_impl(rctx):
    env = "\n".join(["    \"{}\": \"{}\",".format(v, rctx.os.environ.get(v, "")) for v in NONHERMETIC_ENV_VARS])
    home = rctx.os.environ.get("HOME", "")
    rctx.file("env.bzl", "ENV = {{\n{}\n}}\nHOME = \"{}\"".format(env, home))
    rctx.file("BUILD.bazel", "exports_files(glob([\"**\"]))\n")

nonhermetic_repo = repository_rule(
    implementation = _nonhermetic_repo_impl,
    attrs = {},
    environ = NONHERMETIC_ENV_VARS,
)
