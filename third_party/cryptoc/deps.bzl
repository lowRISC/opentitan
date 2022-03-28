# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:git.bzl", "new_git_repository")

def cryptoc_deps():
    new_git_repository(
        name = "cryptoc",
        build_file = Label("//third_party/cryptoc:BUILD.cryptoc.bazel"),
        remote = "https://chromium.googlesource.com/chromiumos/third_party/cryptoc/",
        commit = "e05bfa91102dd5137b4027b4f3405e041ffe2c32",
        shallow_since = "1561753235 -0600",
    )
