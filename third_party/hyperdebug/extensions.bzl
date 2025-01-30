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
        urls = ["https://github.com/lowRISC/hyperdebug-firmware/releases/download/jbk_20250129_01/hyperdebug-firmware.tar.gz"],
        sha256 = "11dacc92b3f3da6b8ad97a4d12aa740bce253f9549b2a909e1e3713476598137",
        build_file = "@lowrisc_opentitan//third_party/hyperdebug:BUILD",
    )
