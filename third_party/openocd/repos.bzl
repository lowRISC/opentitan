# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:git.bzl", "new_git_repository")

def openocd_repos():
    new_git_repository(
        name = "openocd",
        remote = "https://github.com/openocd-org/openocd.git",
        # I started with `branch = "v0.12.0-rc1"`, but new_git_repository()
        # recommended the following values of `commit` and `shallow_since`
        # instead, in order to be reproducible. (Tags can be redefined, but
        # SHA-1 collisions are harder to come by.)
        commit = "5e7612eb4c87e8e7a7000b42ff5d0f7e5c70fc42",
        shallow_since = "1663509167 +0300",
        init_submodules = True,
        build_file = Label("//third_party/openocd:BUILD.openocd_src.bazel"),
    )
