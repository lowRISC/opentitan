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
            url = "https://github.com/lowRISC/crt/archive/v0.4.3.tar.gz",
            strip_prefix = "crt-0.4.3",
            sha256 = "b0d8aa6609f68e29b8a8a1cf5067a44c91b5cb67c4c1d786bcdc3f73e27184ae",
        )
