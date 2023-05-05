# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20230505_02/hyperdebug-firmware.tar.gz"],
        sha256 = "b0d30a237316b969085637c7ee155d2ffa1028d2f89a0af63a633a25914f8d6c",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
