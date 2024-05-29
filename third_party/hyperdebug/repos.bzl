# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20240501_01/hyperdebug-firmware.tar.gz"],
        sha256 = "add2552c940603af0f810f94e4d397ec60f8184722a08e386dcbb91b8e01fe37",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
