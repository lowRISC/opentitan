# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

def rust_repos():
    http_archive(
        name = "rules_rust",
        sha256 = "531bdd470728b61ce41cf7604dc4f9a115983e455d46ac1d0c1632f613ab9fc3",
        strip_prefix = "rules_rust-d8238877c0e552639d3e057aadd6bfcf37592408",
        urls = [
            # `main` branch as of 2021-08-23
            "https://github.com/bazelbuild/rules_rust/archive/d8238877c0e552639d3e057aadd6bfcf37592408.tar.gz",
        ],
    )

    # Boring is only used to build Mundane.
    git_repository(
        name = "boringssl",
        # boringssl `main-with-bazel` branch as of 2021-11-09.
        commit = "4fb158925f7753d80fb858cb0239dff893ef9f15",
        remote = "https://boringssl.googlesource.com/boringssl",
    )

    git_repository(
        name = "mundane",
        commit = "f516499751b45969ac5a95091b1f68cf5ec23f04",
        patch_args = ["-p1"],
        patches = ["//sw/vendor/patches/mundane:build_with_bazel.patch"],
        remote = "https://fuchsia.googlesource.com/mundane",
    )
