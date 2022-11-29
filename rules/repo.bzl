# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def http_archive_or_local(local = None, build_file = None, **kwargs):
    if not local:
        http_archive(build_file = build_file, **kwargs)
    elif build_file:
        native.new_local_repository(
            name = kwargs.get("name"),
            path = local,
            build_file = build_file,
        )
    else:
        native.local_repository(
            name = kwargs.get("name"),
            path = local,
        )
