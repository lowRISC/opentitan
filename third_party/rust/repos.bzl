# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def rust_repos():
    http_archive(
        name = "rules_rust",
        sha256 = "5e2f59778ee496064b2d96182bc8aa916a0e34921124a359f740f51e5e5afc38",
        strip_prefix = "rules_rust-be0d6ca492f64cc8d460f54f467925ef2753ed89",
        url = "https://github.com/lowRISC/rules_rust/archive/be0d6ca492f64cc8d460f54f467925ef2753ed89.tar.gz",
    )

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
