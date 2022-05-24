# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def http_archive_or_local(**kwargs):
    local = kwargs.pop("local", None)
    if local:
        native.local_repository(
            name = kwargs.get("name"),
            path = local,
        )
    else:
        http_archive(**kwargs)
