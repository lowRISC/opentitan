# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@//rules:repo.bzl", "http_archive_or_local")

def rust_repos(rules_rust = None, serde_annotate = None):
    # We use forked/patched Rust Bazel rules to enable caching repository rules
    # required for air-gapped Bazel builds. See lowRISC/opentitan:#15300 for
    # more details.
    http_archive_or_local(
        name = "rules_rust",
        local = rules_rust,
        integrity = "sha256-35cwdTOaqqu4y+aXgIUU2C2PAKMz4+uyJ7/UMIGCmFs=",
        url = "https://github.com/bazelbuild/rules_rust/releases/download/0.47.1/rules_rust-v0.47.1.tar.gz",
        patches = ["//third_party/rust/patches:rules_rust.bindgen_static_lib.patch"],
    )

    http_archive_or_local(
        name = "lowrisc_serde_annotate",
        local = serde_annotate,
        sha256 = "7d6db7c811469f3abd6b58745bd2b8ebb7596a68974739da51bc8b6568c8002a",
        strip_prefix = "serde-annotate-0.0.11",
        url = "https://github.com/lowRISC/serde-annotate/archive/refs/tags/v0.0.11.tar.gz",
    )
