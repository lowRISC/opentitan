# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

NONHERMETIC_ENV_VARS = [
    "HOME",
    "PATH",
    "PYTHONPATH",
    "XILINX_VIVADO",
    "XILINX_HLS",
    "XILINXD_LICENSE_FILE",
]

def _nonhermetic_repo_impl(rctx):
    env = "\n".join(["    \"{}\": \"{}\",".format(v, rctx.os.environ.get(v, "")) for v in NONHERMETIC_ENV_VARS])
    rctx.file("env.bzl", "ENV = {{\n{}\n}}\n".format(env))
    rctx.file("BUILD.bazel", "exports_files(glob([\"**\"]))\n")

nonhermetic_repo = repository_rule(
    implementation = _nonhermetic_repo_impl,
    attrs = {},
    environ = NONHERMETIC_ENV_VARS,
)
