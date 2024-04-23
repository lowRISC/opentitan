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

    # FIXME: The buildtools aren't hacked; the hack is the local name of the repository.
    # We've renamed the repo locally so as to not conflict with the version of buildtools
    # that golang depends on.
    http_archive(
        name = "ot_hack_bazelbuild_buildtools",
        sha256 = "e3bb0dc8b0274ea1aca75f1f8c0c835adbe589708ea89bf698069d0790701ea3",
        strip_prefix = "buildtools-5.1.0",
        url = "https://github.com/bazelbuild/buildtools/archive/refs/tags/5.1.0.tar.gz",
        patches = [
            Label("//third_party/lint:0001-enable-buildifier-test-without-sandbox.patch"),
        ],
        patch_args = ["-p1"],
    )

    http_archive_or_local(
        name = "lowrisc_lint",
        local = lowrisc_lint,
        sha256 = "ff4e14b2a8ace83a7f6a1536c7489c29f8c2b97d345ae9bb8b2d0f68059ec265",
        strip_prefix = "misc-linters-20240423_01",
        url = "https://github.com/lowRISC/misc-linters/archive/refs/tags/20240423_01.tar.gz",
    )
