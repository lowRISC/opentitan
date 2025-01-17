# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

NONHERMETIC_ENV_VARS = [
    "XILINX_VIVADO",
    "XILINXD_LICENSE_FILE",
]

# Binarys that Bazel rule may depend on from the PATH.
NONHERMETIC_BINS = [
    "verilator",
    "vivado",
    "updatemem",
]

def _nonhermetic_repo_impl(rctx):
    env = "\n".join(["    \"{}\": \"{}\",".format(v, rctx.os.environ.get(v, "")) for v in NONHERMETIC_ENV_VARS])
    home = rctx.os.environ.get("HOME", "")

    bins = {name: rctx.which(name) for name in NONHERMETIC_BINS}
    bin_paths = "\n".join(["    \"{}\": \"{}\",".format(name, rctx.path(path).dirname if path != None else "/no-such-path") for name, path in bins.items()])

    rctx.file("env.bzl", "ENV = {{\n{}\n}}\nHOME = \"{}\"\nBIN_PATHS = {{\n{}\n}}\n".format(env, home, bin_paths))
    rctx.file("BUILD.bazel", "exports_files(glob([\"**\"]))\n")

nonhermetic_repo = repository_rule(
    implementation = _nonhermetic_repo_impl,
    attrs = {},
    environ = NONHERMETIC_ENV_VARS,
)
