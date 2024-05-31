# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20240510_01/hyperdebug-firmware.tar.gz"],
        sha256 = "72ce00ab54ea03583085b146ec26c9592bef177737c7635260fe2ab462589d47",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
