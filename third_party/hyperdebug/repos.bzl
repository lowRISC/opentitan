# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20230505_01/hyperdebug-firmware.tar.gz"],
        sha256 = "dfe93a17bcd662b4b10bf30d0a9813158f5ee5f948e025f6e20b280c6da7b7e4",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
