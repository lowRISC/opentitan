# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

shellcheck = module_extension(
    implementation = lambda _: _shellcheck_repos(),
)

def _shellcheck_repos():
    SHELLCHECK_VERSION = "v0.9.0"

    http_archive(
        name = "shellcheck",
        url = "https://github.com/koalaman/shellcheck/releases/download/{version}/shellcheck-{version}.linux.x86_64.tar.xz".format(
            version = SHELLCHECK_VERSION,
        ),
        sha256 = "700324c6dd0ebea0117591c6cc9d7350d9c7c5c287acbad7630fa17b1d4d9e2f",
        strip_prefix = "shellcheck-" + SHELLCHECK_VERSION,
        build_file_content = """
package(default_visibility = ["//visibility:public"])
exports_files(glob(["**"]))
""",
    )
