# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

def protobuf_repos():
    git_repository(
        name = "com_google_protobuf",
        commit = "520c601c99012101c816b6ccc89e8d6fc28fdbb8",
        remote = "https://github.com/protocolbuffers/protobuf",
    )
