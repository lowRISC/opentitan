# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

hyperdebug = module_extension(
    implementation = lambda _: _hyperdebug_repos(),
)

def _hyperdebug_repos():
    http_archive(
        name = "hyperdebug_firmware",
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20241211_02/hyperdebug-firmware.tar.gz"],
        sha256 = "8b72dfe4ecb6a2258228e62c2246c5beffe8339d440a592c483534fa3f54d679",
        build_file = "@lowrisc_opentitan//third_party/hyperdebug:BUILD",
    )
