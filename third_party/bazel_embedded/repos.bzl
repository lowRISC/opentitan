# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@//rules:repo.bzl", "http_archive_or_local")

def bazel_embedded_repos(bazel_embedded = None, platforms = None):
    # Contains rules that support building SW for embedded targets. Specifically, we
    # maintain a fork to build for RISCV32I.
    http_archive_or_local(
        name = "bazel_embedded",
        local = bazel_embedded,
        sha256 = "21a94e15160bad5578a1c93aabeb3e8241113ed9cc976bee80ded2a16713767a",
        strip_prefix = "bazel-embedded-ad7fc22e13e2ff3e9b9470fde1bde15ab31f8a01",
        url = "https://github.com/lowRISC/bazel-embedded/archive/ad7fc22e13e2ff3e9b9470fde1bde15ab31f8a01.tar.gz",
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
