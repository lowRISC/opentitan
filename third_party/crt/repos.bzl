# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:utils.bzl", "maybe")
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def crt_repos(local = None):
    if local:
        native.local_repository(
            name = "crt",
            path = local,
        )
    else:
        maybe(
            http_archive,
            name = "crt",
            url = "https://github.com/troibe/crt/archive/refs/tags/v0.4.17.tar.gz",
            strip_prefix = "crt-0.4.17",
            sha256 = "36e378129c89a45927316a7be9ba6305b047bb4adfd488cf6f15f4542a9452bd",
        )
