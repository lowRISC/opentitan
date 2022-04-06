# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

def bazel_embedded_repos():
    # Contains rules that support building SW for embedded targets. Specifically, we
    # maintain a fork to build for RISCV32I.
    git_repository(
        name = "bazel_embedded",
        commit = "fe65a8aca35ae0bae563efd6a29cc14fcb15140d",
        remote = "https://github.com/lowRISC/bazel-embedded.git",
        shallow_since = "1639417565 -0800",
    )
