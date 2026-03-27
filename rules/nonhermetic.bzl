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

"""Variables that describe non-hermetic parts of the environment.

This repository provides 3 variables:
    - `ENV`
        - Dict of environment variables that may be needed for running non-hermetic tools.
          Currently this only include those needed by Vivado.
    - `HOME`
        - Home directory of the user that invokes Bazel.
          Currently this is used by hsmtool to access user's Google Cloud credentials.
    - `BIN_PATHS`
        - Map from a non-hermetic tool to the part of `$PATH` that contains it.
          This allows actions to use a subset of `$PATH` when invoking the tool,
          as `$PATH` may contain many unrelated tools.

Together, these variables attempt to expose the least amount of environment information
to Bazel rules as possible, thus improves reproducibility and cacheability.
"""

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
