# Copyright lowRISC contributors (OpenTitan project).
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

    http_archive_or_local(
        name = "lowrisc_lint",
        local = lowrisc_lint,
        sha256 = "1303d2790b7d1a0a216558c01f8bc6255dfb840e9e60b523d988b3655a0ddab3",
        strip_prefix = "misc-linters-20240820_01",
        url = "https://github.com/lowRISC/misc-linters/archive/refs/tags/20240820_01.tar.gz",
    )
