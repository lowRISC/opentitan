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
        url = "https://boringssl.googlesource.com/boringssl/+archive/4fb158925f7753d80fb858cb0239dff893ef9f15.tar.gz",
    )

    http_archive(
        name = "mundane",
        url = "https://fuchsia.googlesource.com/mundane/+archive/f516499751b45969ac5a95091b1f68cf5ec23f04.tar.gz",
        patch_args = ["-p1"],
        patches = ["//sw/vendor/patches/mundane:build_with_bazel.patch"],
    )
