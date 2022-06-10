# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@//rules:repo.bzl", "http_archive_or_local")

def bazel_embedded_repos(bazel_embedded = None, platforms = None):
    # Contains rules that support building SW for embedded targets. Specifically, we
    # maintain a fork to build for RISCV32I.
    commit = "322dd944eb6b2f1c7736d854ff3026840f3ef8f3"
    fork = "lowRISC"
    http_archive_or_local(
        name = "bazel_embedded",
        local = bazel_embedded,
        sha256 = "278562634fb0261bc85c9da3ed003eba86430a56bd4668cc742779c3fa085fec",
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
