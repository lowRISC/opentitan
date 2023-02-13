# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@//rules:repo.bzl", "http_archive_or_local")

def rust_repos(rules_rust = None, safe_ftdi = None, serde_annotate = None):
    # We use forked/patched Rust Bazel rules to enable caching repository rules
    # required for air-gapped Bazel builds. See lowRISC/opentitan:#15300 for
    # more details.
    http_archive_or_local(
        name = "rules_rust",
        local = rules_rust,
        sha256 = "322003618cd248ab9a85f055920859132ef81a2c73a0c9fc3816c74cb8fd9f6b",
        strip_prefix = "rules_rust-rebase-20230213_01",
        url = "https://github.com/lowRISC/rules_rust/archive/refs/tags/rebase-20230213_01.tar.gz",
    )

    http_archive_or_local(
        name = "lowrisc_safe_ftdi",
        local = safe_ftdi,
        sha256 = "2dc6744f4bf6f95fbe51befb9316a0a33f70291856fef8bd85157a387659e527",
        strip_prefix = "safe-ftdi-bazel-20230213_01",
        url = "https://github.com/lowRISC/safe-ftdi/archive/refs/tags/bazel-20230213_01.tar.gz",
    )

    http_archive_or_local(
        name = "lowrisc_serde_annotate",
        local = serde_annotate,
        sha256 = "8772091928c47bf8c22e8ecdec049e1558993c9855ff9fd4a05daad77596ce9e",
        strip_prefix = "serde-annotate-0.0.7",
        url = "https://github.com/lowRISC/serde-annotate/archive/refs/tags/v0.0.7.tar.gz",
    )
