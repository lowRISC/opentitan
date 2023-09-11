# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20230911_01/hyperdebug-firmware.tar.gz"],
        sha256 = "695600f7466839a16214b4a39a9be3a5802a158dc89de9862a31390e56f0bec4",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
