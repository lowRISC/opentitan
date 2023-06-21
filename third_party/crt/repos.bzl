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
            url = "https://github.com/luismarques/crt/archive/7427f78605b1b19bda2b25dca238368582af165d.tar.gz",
            strip_prefix = "crt-7427f78605b1b19bda2b25dca238368582af165d",
            sha256 = "6b1106e1495f67ab70bc23f5279423224a206bf077d4012cf5169ec842a20f78",
        )
