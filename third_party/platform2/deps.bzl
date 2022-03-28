# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:git.bzl", "new_git_repository")

def platform2_deps():
    new_git_repository(
        name = "chromiumos_platform2",
        build_file = Label("//third_party/platform2:BUILD.platform2.bazel"),
        remote = "https://chromium.googlesource.com/chromiumos/platform2/",
        commit = "8ff08453c2223c1269b2d6127bfdfd32e3038ada",
    )
