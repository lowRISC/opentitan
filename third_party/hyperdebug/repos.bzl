# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20231129_01/hyperdebug-firmware.tar.gz"],
        sha256 = "de1e1dabf305eac5d3b1384b65d0b9684a345fdea5299c450bad773ef73b9636",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
