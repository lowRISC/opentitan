# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def qemu_opentitan_repos():
    QEMU_VERSION = "v9.2.0-2025-02-11"

    url = "/".join([
        "https://github.com/lowRISC/qemu/releases/download",
        QEMU_VERSION,
        "qemu-ot-earlgrey-{}-x86_64-unknown-linux-gnu.tar.gz".format(QEMU_VERSION),
    ])

    http_archive(
        name = "qemu_opentitan",
        url = url,
        build_file = Label(":BUILD.qemu_opentitan.bazel"),
        sha256 = "85091287ee67dee337968071b7d10d39d44bb582c90991eae3d61f11a13ccf29",
    )

qemu = module_extension(
    implementation = lambda _: qemu_opentitan_repos(),
)
