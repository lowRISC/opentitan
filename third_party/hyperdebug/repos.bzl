# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20240529_01/hyperdebug-firmware.tar.gz"],
        sha256 = "1ed9231800d6bf42ad28b5e44708bbcb63bb9611191be8886861970b0c58909d",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
