# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:repo.bzl", "http_archive_or_local")

def google_repos(
        platforms = None,
        rules_cc = None,
        rules_pkg = None,
        absl = None,
        googletest = None):
    http_archive_or_local(
        name = "platforms",
        local = platforms,
        url = "https://github.com/bazelbuild/platforms/releases/download/0.0.10/platforms-0.0.10.tar.gz",
        sha256 = "218efe8ee736d26a3572663b374a253c012b716d8af0c07e842e82f238a0a7ee",
    )

    http_archive_or_local(
        name = "rules_cc",
        local = rules_cc,
        sha256 = "2037875b9a4456dce4a79d112a8ae885bbc4aad968e6587dca6e64f3a0900cdf",
        strip_prefix = "rules_cc-0.0.9",
        url = "https://github.com/bazelbuild/rules_cc/releases/download/0.0.9/rules_cc-0.0.9.tar.gz",
    )

    http_archive_or_local(
        name = "rules_pkg",
        local = rules_pkg,
        urls = [
            "https://mirror.bazel.build/github.com/bazelbuild/rules_pkg/releases/download/0.7.0/rules_pkg-0.7.0.tar.gz",
            "https://github.com/bazelbuild/rules_pkg/releases/download/0.7.0/rules_pkg-0.7.0.tar.gz",
        ],
        sha256 = "8a298e832762eda1830597d64fe7db58178aa84cd5926d76d5b744d6558941c2",
    )

    http_archive_or_local(
        name = "abseil-cpp",
        local = absl,
        sha256 = "59d2976af9d6ecf001a81a35749a6e551a335b949d34918cfade07737b9d93c5",
        strip_prefix = "abseil-cpp-20230802.0",
        url = "https://github.com/abseil/abseil-cpp/archive/refs/tags/20230802.0.tar.gz",
    )

    http_archive_or_local(
        name = "googletest",
        local = googletest,
        sha256 = "353571c2440176ded91c2de6d6cd88ddd41401d14692ec1f99e35d013feda55a",
        strip_prefix = "googletest-release-1.11.0",
        url = "https://github.com/google/googletest/archive/refs/tags/release-1.11.0.zip",
    )

    http_archive_or_local(
        name = "rules_foreign_cc",
        strip_prefix = "rules_foreign_cc-0.9.0",
        sha256 = "2a4d07cd64b0719b39a7c12218a3e507672b82a97b98c6a89d38565894cf7c51",
        url = "https://github.com/bazelbuild/rules_foreign_cc/archive/refs/tags/0.9.0.tar.gz",
    )

def fuzzing_repos():
    http_archive_or_local(
        name = "rules_fuzzing",
        sha256 = "e6bc219bfac9e1f83b327dd090f728a9f973ee99b9b5d8e5a184a2732ef08623",
        strip_prefix = "rules_fuzzing-0.5.2",
        urls = ["https://github.com/bazelbuild/rules_fuzzing/releases/download/v0.5.2/rules_fuzzing-0.5.2.zip"],
    )
