# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20240216_01/hyperdebug-firmware.tar.gz"],
        sha256 = "cb932b41a20952f32130d9154e33feece9f09ae7dca0d0b88f9bcdc8a13dedba",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
