# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20240125_01/hyperdebug-firmware.tar.gz"],
        sha256 = "cabcd31873ba14f15b5d0a0b9ddbf510c7c6416c2f5d151aea01a0e91297c2a8",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
