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
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20250129_01/hyperdebug-firmware.tar.gz"],
        sha256 = "ac529cb2f54149b0a0681b37ebd64e4ced095cd59b3d335e812a71d3d28a047f",
        build_file = "@lowrisc_opentitan//third_party/hyperdebug:BUILD",
    )
