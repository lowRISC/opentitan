# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20230922_01/hyperdebug-firmware.tar.gz"],
        sha256 = "b9171be8e8d9d2327670f1a058408535d0332579be59f367e040915acb4e1f35",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
