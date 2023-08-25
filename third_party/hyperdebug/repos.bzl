# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20230823_02/hyperdebug-firmware.tar.gz"],
        sha256 = "f58516660b86769a34680a80b9ac65a47296f64669a9a6f5cee805abc2f42ac1",
        build_file = "@//third_party/hyperdebug:BUILD",
    )
