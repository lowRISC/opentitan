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
        sha256 = "63fe16ec30c0fa64bb27f537c0185eb4c8701a91c2a1200aa61d4034e176020f",
        strip_prefix = "misc-linters-b08fcf19d28ed565e4f5081bbde0607a7a6f74cc",
        url = "https://github.com/lowrisc/misc-linters/archive/b08fcf19d28ed565e4f5081bbde0607a7a6f74cc.tar.gz",
    )
