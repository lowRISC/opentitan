# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20231101_01/hyperdebug-firmware.tar.gz"],
        sha256 = "944297f725152df83b6c4396a1bb313a5c89efc3ddaeedb4e90ff0dd63b82f31",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
