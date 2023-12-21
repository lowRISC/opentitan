# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20231221_01/hyperdebug-firmware.tar.gz"],
        sha256 = "f58e79737ced25fa8252cd6414a8ef11a336b308e2816e78e2f1759017812520",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
