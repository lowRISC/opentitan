# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def bazel_embedded_repos(local = None):
    # Contains rules that support building SW for embedded targets. Specifically, we
    # maintain a fork to build for RISCV32I.
    if local:
        native.local_repository(
            name = "bazel_embedded",
            path = local,
        )
    else:
        http_archive(
            name = "bazel_embedded",
            sha256 = "278562634fb0261bc85c9da3ed003eba86430a56bd4668cc742779c3fa085fec",
            strip_prefix = "bazel-embedded-322dd944eb6b2f1c7736d854ff3026840f3ef8f3",
            url = "https://github.com/lowRISC/bazel-embedded/archive/322dd944eb6b2f1c7736d854ff3026840f3ef8f3.tar.gz",
        )

    # The platforms repo contains standard cpu/os/disto contraints.
    http_archive(
        name = "platforms",
        urls = [
            "https://mirror.bazel.build/github.com/bazelbuild/platforms/releases/download/0.0.5/platforms-0.0.5.tar.gz",
            "https://github.com/bazelbuild/platforms/releases/download/0.0.5/platforms-0.0.5.tar.gz",
        ],
        sha256 = "379113459b0feaf6bfbb584a91874c065078aa673222846ac765f86661c27407",
    )
