# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def protobuf_repos():
    http_archive(
        name = "com_google_protobuf",
        sha256 = "3bd7828aa5af4b13b99c191e8b1e884ebfa9ad371b0ce264605d347f135d2568",
        strip_prefix = "protobuf-3.19.4",
        urls = [
            "https://github.com/protocolbuffers/protobuf/archive/v3.19.4.tar.gz",
        ],
    )
