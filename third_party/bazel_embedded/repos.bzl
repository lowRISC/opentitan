# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def bazel_embedded_repos():
    # Contains rules that support building SW for embedded targets. Specifically, we
    # maintain a fork to build for RISCV32I.
    http_archive(
        name = "bazel_embedded",
        sha256 = "ee828762c3b7ea6f4513a57bf39b530671822503be924d3fe29e48390ca41bca",
        strip_prefix = "bazel-embedded-fe65a8aca35ae0bae563efd6a29cc14fcb15140d",
        url = "https://github.com/lowRISC/bazel-embedded/archive/fe65a8aca35ae0bae563efd6a29cc14fcb15140d.tar.gz",
    )
