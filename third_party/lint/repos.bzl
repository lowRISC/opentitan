# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def lint_repos():
    # We have a 'vendored' copy of the google_verible_verilog_syntax_py repo
    native.local_repository(
        name = "google_verible_verilog_syntax_py",
        path = "hw/ip/prim/util/vendor/google_verible_verilog_syntax_py",
    )

    http_archive(
        name = "com_github_bazelbuild_buildtools",
        strip_prefix = "buildtools-main",
        url = "https://github.com/bazelbuild/buildtools/archive/main.zip",
    )

    http_archive(
        name = "lowrisc_lint",
        sha256 = "cb4eeef665f99dea13b1202eb04c1889f412f248c9ea7547b40d300e01dea7d2",
        strip_prefix = "misc-linters-b5a926d6cce8d6e78291f91999c3cd2025ba1d5b",
        url = "https://github.com/lowRISC/misc-linters/archive/b5a926d6cce8d6e78291f91999c3cd2025ba1d5b.tar.gz",
    )
