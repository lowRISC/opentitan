# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
load("//rules:dynamic_archive.bzl", "dynamic_archive")

def rust_repos():
    http_archive(
        name = "rules_rust",
        sha256 = "531bdd470728b61ce41cf7604dc4f9a115983e455d46ac1d0c1632f613ab9fc3",
        strip_prefix = "rules_rust-d8238877c0e552639d3e057aadd6bfcf37592408",
        url = "https://github.com/bazelbuild/rules_rust/archive/d8238877c0e552639d3e057aadd6bfcf37592408.tar.gz",
    )

    # Boring is only used to build Mundane.
    dynamic_archive(
        name = "boringssl",
        sha256 = "9b0e6195cf7270149f7719467c284f4882bdfb7a6c288fb9ca6618ef2e3dc83f",
        urls = ["https://boringssl.googlesource.com/boringssl/+archive/4fb158925f7753d80fb858cb0239dff893ef9f15.tar.gz"],
    )

    dynamic_archive(
        name = "mundane",
        sha256 = "583d5cacb3c6c68c65c59d69786c0563bd9bbcebe8c375a81bc51e9b016332c7",
        urls = ["https://fuchsia.googlesource.com/mundane/+archive/f516499751b45969ac5a95091b1f68cf5ec23f04.tar.gz"],
        patch_args = ["-p1"],
        patches = ["//sw/vendor/patches/mundane:build_with_bazel.patch"],
    )
