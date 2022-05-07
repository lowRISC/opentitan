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
        sha256 = "da0a3c8cdf9db4c8f48fc398c7fb9bc25ac1037497e61ab2fa77beb81e67bee2",
        strip_prefix = "misc-linters-3c21d91af6115f3e0fb6584a9d62d4a0b27b6ccf",
        url = "https://github.com/lowRISC/misc-linters/archive/3c21d91af6115f3e0fb6584a9d62d4a0b27b6ccf.tar.gz",
    )
