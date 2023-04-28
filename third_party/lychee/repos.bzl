# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:repo.bzl", "http_archive_or_local")

def lychee_repos(local = None):
    LYCHEE_VERSION = "v0.11.1"

    url = "/".join([
        "https://github.com/lycheeverse/lychee/releases/download",
        LYCHEE_VERSION,
        "lychee-{}-x86_64-unknown-linux-gnu.tar.gz".format(LYCHEE_VERSION),
    ])

    http_archive_or_local(
        name = "lychee",
        url = url,
        local = local,
        build_file_content = """
package(default_visibility = ["//visibility:public"])
exports_files(glob(["**"]))
""",
        sha256 = "2cb75e6bcaf97f049d4e0260433938a77c60d39bd347d704502ae96c1e6f481c",
    )
