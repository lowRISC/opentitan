# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:repo.bzl", "http_archive_or_local")

def shellcheck_repos(local = None):
    SHELLCHECK_VERSION = "v0.8.0"

    http_archive_or_local(
        name = "shellcheck",
        local = local,
        url = "https://github.com/koalaman/shellcheck/releases/download/{version}/shellcheck-{version}.linux.x86_64.tar.xz".format(
            version = SHELLCHECK_VERSION,
        ),
        sha256 = "ab6ee1b178f014d1b86d1e24da20d1139656c8b0ed34d2867fbb834dad02bf0a",
        strip_prefix = "shellcheck-" + SHELLCHECK_VERSION,
        build_file_content = """
package(default_visibility = ["//visibility:public"])
exports_files(glob(["**"]))
""",
    )
