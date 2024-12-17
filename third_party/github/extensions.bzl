# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

github_tools = module_extension(
    implementation = lambda _: _github_tools_repos(),
)

def _github_tools_repos():
    http_archive(
        name = "com_github_gh",
        url = "https://github.com/cli/cli/releases/download/v2.13.0/gh_2.13.0_linux_amd64.tar.gz",
        sha256 = "9e833e02428cd49e0af73bc7dc4cafa329fe3ecba1bfe92f0859bf5b11916401",
        build_file = Label("//third_party/github:BUILD.gh.bazel"),
        strip_prefix = "gh_2.13.0_linux_amd64",
    )
