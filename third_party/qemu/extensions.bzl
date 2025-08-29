# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def _qemu_opentitan_repos():
    QEMU_VERSION = "9.2.0-2025-02-11"
    http_archive(
        name = "qemu_opentitan",
        url = "https://github.com/lowRISC/qemu/archive/refs/tags/v{}.tar.gz".format(QEMU_VERSION),
        build_file = Label(":BUILD.qemu_opentitan.bazel"),
        strip_prefix = "qemu-{}".format(QEMU_VERSION),
        sha256 = "46afbfeec901cf4c75e26630e2a404e002d3b865660d28c2745c4a0e0de621d0",
    )

qemu = module_extension(
    implementation = lambda _: _qemu_opentitan_repos(),
)
