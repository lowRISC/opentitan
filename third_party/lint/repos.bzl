# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
load("//rules:repo.bzl", "http_archive_or_local")

def lint_repos(lowrisc_lint = None):
    # We have a 'vendored' copy of the google_verible_verilog_syntax_py repo
    native.local_repository(
        name = "google_verible_verilog_syntax_py",
        path = "hw/ip/prim/util/vendor/google_verible_verilog_syntax_py",
    )

    http_archive(
        name = "com_github_bazelbuild_buildtools",
        sha256 = "e3bb0dc8b0274ea1aca75f1f8c0c835adbe589708ea89bf698069d0790701ea3",
        strip_prefix = "buildtools-5.1.0",
        url = "https://github.com/bazelbuild/buildtools/archive/refs/tags/5.1.0.tar.gz",
    )

    http_archive_or_local(
        name = "lowrisc_lint",
        local = lowrisc_lint,
        sha256 = "0b3b7b8f5ceacda50ca74a5b7dfeddcbd5ddfa8ffd1a482878aee2fc02989794",
        strip_prefix = "misc-linters-20220921_01",
        url = "https://github.com/lowRISC/misc-linters/archive/refs/tags/20220921_01.tar.gz"
    )
