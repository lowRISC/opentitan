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
            sha256 = "2af581b33bf7e8ce702b31fc38ae59ee846ae01d6237ad507c83991eb529826b",
            strip_prefix = "bazel-embedded-e3e26097f3fe8775670c7031bf03a49e75873a02",
            url = "https://github.com/lowRISC/bazel-embedded/archive/e3e26097f3fe8775670c7031bf03a49e75873a02.tar.gz",
        )
