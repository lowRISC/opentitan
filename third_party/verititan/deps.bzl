# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:git.bzl", "new_git_repository")

def verititan_deps():
    new_git_repository(
        name = "verititan",
        build_file = Label("//third_party/verititan:BUILD.verititan.bazel"),
        remote = "https://github.com/secure-foundations/veri-titan.git",
        commit = "6e0137bbbebf851518bd7121d01c986c43ab552d",
        shallow_since = "1642479167 -0500",
    )
