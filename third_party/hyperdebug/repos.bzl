# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20230419_01/hyperdebug-firmware.tar.gz"],
        sha256 = "c0057273ae05a9970245256c376a719d01a53981ae3081e8282541e319081370",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
