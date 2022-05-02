# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
load("@//rules:repo.bzl", "http_archive_or_local")

def rust_repos(rules_rust = None, safe_ftdi = None):
    # We use forked/patched Rust Bazel rules to enable caching repository rules
    # required for air-gapped Bazel builds. See lowRISC/opentitan:#12515 for
    # more details.
    http_archive_or_local(
        name = "rules_rust",
        local = rules_rust,
        sha256 = "7ee424554cce89befd439b553ef9094d68ccbcbf33013194bd0effa1d4463a9b",
        strip_prefix = "rules_rust-repo-cache-20220601_01",
        url = "https://github.com/lowRISC/rules_rust/archive/refs/tags/repo-cache-20220601_01.tar.gz",
    )

    http_archive_or_local(
        name = "safe_ftdi",
        local = safe_ftdi,
        sha256 = "33c61f3c2303e595c554a0b9ed8ba7ae3088d51052fa5916a9a4767604683b52",
        strip_prefix = "safe-ftdi-bazel-20220511_01",
        url = "https://github.com/lowRISC/safe-ftdi/archive/refs/tags/bazel-20220511_01.tar.gz",
    )

    # We use GitHub mirrors of boringssl and mundane because their counterparts
    # hosted on Google's git platform do not provide stable sha256 hashes that
    # that enable caching these dependencies for air-gapped Bazel builds.

    # Boring is only used to build Mundane.
    http_archive(
        name = "boringssl",
        sha256 = "e168777eb0fc14ea5a65749a2f53c095935a6ea65f38899a289808fb0c221dc4",
        strip_prefix = "boringssl-4fb158925f7753d80fb858cb0239dff893ef9f15",
        url = "https://github.com/lowRISC/boringssl/archive/4fb158925f7753d80fb858cb0239dff893ef9f15.tar.gz",
    )

    http_archive(
        name = "mundane",
        sha256 = "97f54f1e00778da802e983116d639033cffa366d1370348aeb6228a82658b206",
        strip_prefix = "mundane-f516499751b45969ac5a95091b1f68cf5ec23f04",
        url = "https://github.com/lowRISC/mundane/archive/f516499751b45969ac5a95091b1f68cf5ec23f04.tar.gz",
        patch_args = ["-p1"],
        patches = ["//sw/vendor/patches/mundane:build_with_bazel.patch"],
    )
