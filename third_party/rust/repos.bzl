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
        sha256 = "fe8d7e62d093e10d8f87b9fd26e4ee2b8d64667ab6827f41fb38eda640233e0f",
        strip_prefix = "rules_rust-add-missing-rv32-shas-20221031_01",
        url = "https://github.com/lowRISC/rules_rust/archive/refs/tags/add-missing-rv32-shas-20221031_01.tar.gz",
    )

    http_archive_or_local(
        name = "safe_ftdi",
        local = safe_ftdi,
        sha256 = "33c61f3c2303e595c554a0b9ed8ba7ae3088d51052fa5916a9a4767604683b52",
        strip_prefix = "safe-ftdi-bazel-20220511_01",
        url = "https://github.com/lowRISC/safe-ftdi/archive/refs/tags/bazel-20220511_01.tar.gz",
    )

    http_archive_or_local(
        name = "serde_annotate",
        local = serde_annotate,
        sha256 = "e5d82f7519eac85daa5b52d85c597285ba761cad7138694c222be102346421ae",
        strip_prefix = "serde-annotate-0.0.3",
        url = "https://github.com/lowRISC/serde-annotate/archive/refs/tags/v0.0.3.tar.gz",
    )
