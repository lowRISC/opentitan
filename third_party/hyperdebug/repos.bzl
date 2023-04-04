# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:utils.bzl", "maybe")
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    maybe(
        http_archive,
        name = "lowrisc_hyperdebug",
        url = "https://github.com/lowRISC/hyperdebug-firmware/releases/download/20230404_01/hyperdebug-firmware.tar.gz",
        sha256 = "6030cf28196d63256a30c980825b635df139e70c098309bfa04f5e85c1b722e3",
        strip_prefix = "hyperdebug",
        build_file_content = "exports_files(glob([\"**\"]))",
    )
