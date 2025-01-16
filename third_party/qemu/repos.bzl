# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def qemu_opentitan_repos():
    QEMU_VERSION = "v9.1.0-2025-01-28"

    url = "/".join([
        "https://github.com/lowRISC/qemu/releases/download",
        QEMU_VERSION,
        "qemu-ot-earlgrey-{}-x86_64-unknown-linux-gnu.tar.gz".format(QEMU_VERSION),
    ])

    http_archive(
        name = "qemu_opentitan",
        url = url,
        build_file = Label(":BUILD.qemu_opentitan.bazel"),
        sha256 = "530bb7568f17ba3f9ba1245388c2625259d180188c8c5c9e15634b942ebeb108",
    )
