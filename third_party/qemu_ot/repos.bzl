# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:repo.bzl", "http_archive_or_local")

def qemu_ot_repos(local = None):
    QEMU_OT_VERSION = "v8.0.2-2023-09-07"

    url = "/".join([
        "https://github.com/lowRISC/qemu/releases/download",
        QEMU_OT_VERSION,
        "qemu-ot-earlgrey-{}-x86_64-unknown-linux-gnu.tar.gz".format(QEMU_OT_VERSION),
    ])

    # FIXME: @crt already defines @qemu but that's the vanilla QEMU, not the OT port
    http_archive_or_local(
        name = "qemu-ot",
        url = url,
        local = local,
        build_file_content = """
package(default_visibility = ["//visibility:public"])
exports_files(glob(["**"]))
""",
        sha256 = "89451f9e613db10814776e15661564854edde322129da4afb491b4bad3f48e25",
    )
