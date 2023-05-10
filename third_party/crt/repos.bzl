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
            url = "https://github.com/lowRISC/crt/archive/7570742152a36b47f7557b7a099319b9d4e5b144.tar.gz",
            strip_prefix = "crt-7570742152a36b47f7557b7a099319b9d4e5b144",
            sha256 = "6add5fae477f73127381044958557bda97a61b825fe1fe023ad326b3d3dcad00",
        )
