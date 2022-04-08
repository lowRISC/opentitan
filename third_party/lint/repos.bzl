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
        sha256 = "2cf2badc52b212445d7ed6eb4d99a925d9736b06daacf9ad3b783953fb3ccaee",
        strip_prefix = "misc-linters-8bca6cff6f5def9ba866a11b7eeb3f4a12f9f516",
        url = "https://github.com/lowrisc/misc-linters/archive/8bca6cff6f5def9ba866a11b7eeb3f4a12f9f516.tar.gz",
    )
