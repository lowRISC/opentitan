# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def rust_repos():
    http_archive(
        name = "rules_rust",
        sha256 = "531bdd470728b61ce41cf7604dc4f9a115983e455d46ac1d0c1632f613ab9fc3",
        strip_prefix = "rules_rust-d8238877c0e552639d3e057aadd6bfcf37592408",
        url = "https://github.com/bazelbuild/rules_rust/archive/d8238877c0e552639d3e057aadd6bfcf37592408.tar.gz",
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
