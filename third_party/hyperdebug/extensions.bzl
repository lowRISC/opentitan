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
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/20250131_01/hyperdebug-firmware.tar.gz"],
        sha256 = "8595340b347531438ce07f7d678ec24038b4fa2edd7f4a620bd8c5130d72c2ce",
        build_file = "@lowrisc_opentitan//third_party/hyperdebug:BUILD",
    )
