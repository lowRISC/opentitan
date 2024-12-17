# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
load("//rules:repo.bzl", "http_archive_or_local")

def lint_repos(lowrisc_misc_linters = None):
    # We have a 'vendored' copy of the google_verible_verilog_syntax_py repo
    native.local_repository(
        name = "google_verible_verilog_syntax_py",
        path = "hw/ip/prim/util/vendor/google_verible_verilog_syntax_py",
    )

    http_archive_or_local(
        name = "lowrisc_misc_linters",
        local = lowrisc_misc_linters,
        sha256 = "365fe67d8168fee1a0fc3aea4bb80588bf721dc4fc83b40463b09eb50897cda3",
        strip_prefix = "misc-linters-20240823_01",
        url = "https://github.com/lowRISC/misc-linters/archive/refs/tags/20240823_01.tar.gz",
    )
