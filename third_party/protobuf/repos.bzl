# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def protobuf_repos():
    http_archive(
        name = "com_google_protobuf",
        sha256 = "e661431858c1c7672a77446a7732d397dc5ae422eddfe07d02ed2c0619ae5d2b",
        strip_prefix = "protobuf-520c601c99012101c816b6ccc89e8d6fc28fdbb8",
        url = "https://github.com/protocolbuffers/protobuf/archive/520c601c99012101c816b6ccc89e8d6fc28fdbb8.tar.gz",
    )
