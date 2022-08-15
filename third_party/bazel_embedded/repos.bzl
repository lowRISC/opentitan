# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@//rules:repo.bzl", "http_archive_or_local")

def bazel_embedded_repos(bazel_embedded = None, platforms = None):
    # Contains rules that support building SW for embedded targets. Specifically, we
    # maintain a fork to build for RISCV32I.
    commit = "a274de4b4c51d8a9fb76c153fd66b4b1703ae872"
    fork = "lowRISC"
    http_archive_or_local(
        name = "bazel_embedded",
        local = bazel_embedded,
        sha256 = "6ccd63a2f71c3dd6b35d2917e903217c20288c162f80578d48ea3a8a14a60c68",
        strip_prefix = "bazel-embedded-{}".format(commit),
        url = "https://github.com/{}/bazel-embedded/archive/{}.tar.gz".format(fork, commit),
    )

    # The platforms repo contains standard cpu/os/disto contraints.
    http_archive_or_local(
        name = "platforms",
        local = platforms,
        urls = [
            "https://mirror.bazel.build/github.com/bazelbuild/platforms/releases/download/0.0.5/platforms-0.0.5.tar.gz",
            "https://github.com/bazelbuild/platforms/releases/download/0.0.5/platforms-0.0.5.tar.gz",
        ],
        sha256 = "379113459b0feaf6bfbb584a91874c065078aa673222846ac765f86661c27407",
    )
