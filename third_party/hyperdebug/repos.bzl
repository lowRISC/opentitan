# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20230509_01/hyperdebug-firmware.tar.gz"],
        sha256 = "d25cffd7d5a1e6666855f4226064af644a43cc7372017cbb27787e0ae9306f6e",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
