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
            url = "https://github.com/lowRISC/crt/archive/refs/tags/v0.4.7.tar.gz",
            strip_prefix = "crt-0.4.7",
            sha256 = "92ab725c9b0b6b09e25b9cc70158d47d53275899ec53edfa95e69ebf114cbaa2",
        )
