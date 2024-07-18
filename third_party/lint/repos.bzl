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

    # FIXME: The buildtools aren't hacked; the hack is the local name of the repository.
    # We've renamed the repo locally so as to not conflict with the version of buildtools
    # that golang depends on.
    http_archive(
        name = "ot_hack_bazelbuild_buildtools",
        sha256 = "05c3c3602d25aeda1e9dbc91d3b66e624c1f9fdadf273e5480b489e744ca7269",
        strip_prefix = "buildtools-6.4.0",
        url = "https://github.com/bazelbuild/buildtools/archive/refs/tags/v6.4.0.tar.gz",
    )

    http_archive_or_local(
        name = "lowrisc_lint",
        local = lowrisc_lint,
        sha256 = "4797c7041e97e818d3d9df29909d6e3e13d68cf08519f080232ef91173dcad90",
        strip_prefix = "misc-linters-20240722-01",
        url = "https://github.com/jwnrt/misc-linters/archive/refs/tags/20240722-01.tar.gz",
    )
