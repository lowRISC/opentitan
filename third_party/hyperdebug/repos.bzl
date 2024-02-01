# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20240411_01/hyperdebug-firmware.tar.gz"],
        sha256 = "43fd0425856765bbe11fc344fb797f8c08eb5d733bc244c6385a2cb272f5a5fd",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
