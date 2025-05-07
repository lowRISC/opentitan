# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20241206_01/hyperdebug-firmware.tar.gz"],
        sha256 = "13612708d0d71e340babff07d14d67cd9d51f2eb3c370757c3aa905aeab13d1b",
        build_file = "@lowrisc_opentitan//third_party/hyperdebug:BUILD",
    )
