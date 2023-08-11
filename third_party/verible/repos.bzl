# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:repo.bzl", "http_archive_or_local")

def verible_repos(local = None):
    VERIBLE_VERSION = "v0.0-3410-g398a8505"

    http_archive_or_local(
        name = "verible",
        local = local,
        url = "https://github.com/chipsalliance/verible/releases/download/{version}/verible-{version}-linux-static-x86_64.tar.gz".format(
            version = VERIBLE_VERSION,
        ),
        sha256 = "c1e6b6ff514a737c3e9a2330628a057b48d5042be72f67a68864d7d4fc35e72d",
        strip_prefix = "verible-" + VERIBLE_VERSION,
        build_file_content = """
package(default_visibility = ["//visibility:public"])
exports_files(glob(["**"]))
""",
    )
