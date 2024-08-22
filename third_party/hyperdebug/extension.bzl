# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20240621_01/hyperdebug-firmware.tar.gz"],
        sha256 = "649a8cd6d183bc3fb286ea5895c752cfec3aa29b9990f44bb9e7621c0414c7de",
        build_file = "@//third_party/hyperdebug:BUILD",
    )

hyperdebug = module_extension(
    implementation = lambda _: hyperdebug_repos(),
)
