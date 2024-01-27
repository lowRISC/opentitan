# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20240209_01/hyperdebug-firmware.tar.gz"],
        sha256 = "03c58b220828fc88c9a23ec1b6e93f210354687a5dccd9b957aaaf45f75f82f0",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
