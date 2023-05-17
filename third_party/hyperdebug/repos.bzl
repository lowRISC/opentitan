# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20230517_01/hyperdebug-firmware.tar.gz"],
        sha256 = "df79a383c826dab275281e90a4473e16275b41c5cd346e1fea33137a169a0656",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
