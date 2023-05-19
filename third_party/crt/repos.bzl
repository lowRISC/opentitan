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
            url = "https://github.com/lowRISC/crt/archive/v0.4.4.tar.gz",
            strip_prefix = "crt-0.4.4",
            sha256 = "811f644613f80c6af44e64197c251286c2f205931dcbef9ea80c4dbd8ed1df60",
        )
