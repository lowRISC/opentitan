# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

serde_annotate = module_extension(
    implementation = lambda _: _serde_annotate_repo(),
)

def _serde_annotate_repo():
    http_archive(
        name = "lowrisc_serde_annotate",
        sha256 = "7d6db7c811469f3abd6b58745bd2b8ebb7596a68974739da51bc8b6568c8002a",
        strip_prefix = "serde-annotate-0.0.11",
        url = "https://github.com/lowRISC/serde-annotate/archive/refs/tags/v0.0.11.tar.gz",
    )
