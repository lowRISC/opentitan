# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20240112_01/hyperdebug-firmware.tar.gz"],
        sha256 = "71942c4aabbc93fe3ec49c631009a30028f07658b36c803b40ffb348b915abef",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
