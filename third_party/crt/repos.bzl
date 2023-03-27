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
            url = "https://github.com/lowRISC/crt/archive/refs/tags/v0.3.10.tar.gz",
            sha256 = "3514e15cd7ae7d3243864fdce6ea483cbbeb1b45c4c09a2a70f75376e9ea3934",
            strip_prefix = "crt-0.3.10",
        )
