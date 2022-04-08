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
            sha256 = "ef976ed293199f4c072812c951883b223867a4ef6793b3a795bddbc197b53d4f",
            strip_prefix = "bazel-embedded-09618f3535d90f8130ffdc27df311039f62ae872",
            url = "https://github.com/lowRISC/bazel-embedded/archive/09618f3535d90f8130ffdc27df311039f62ae872.tar.gz",
        )
