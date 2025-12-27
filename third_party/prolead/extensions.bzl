# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def _prolead_repos():
    COMMIT = "7ed0f9f2afe2d1294fb15a48501d489641d70820"

    http_archive(
        name = "prolead",
        build_file = Label("//third_party/prolead:BUILD.bazel"),
        strip_prefix = "PROLEAD-" + COMMIT,
        urls = [
            "https://github.com/ChairImpSec/PROLEAD/archive/{}.zip".format(COMMIT),
        ],
        integrity = "sha256-Et9OhCkH+zXlrklrE83/2StitSaFwzrsfW+g7Xw9m3U=",
    )
    http_archive(
        name = "boost",
        build_file_content = """
package(default_visibility = ["//visibility:public"])

filegroup(
    name = "headers",
    srcs = glob(["boost/**/*"]),
)

filegroup(
    name = "root_anchor",
    srcs = ["boost/version.hpp"],
)
""",
        strip_prefix = "boost_1_83_0",
        urls = ["https://archives.boost.io/release/1.83.0/source/boost_1_83_0.tar.bz2"],
        sha256 = "6478edfe2f3305127cffe8caf73ea0176c53769f4bf1585be237eb30798c3b8e",
    )

prolead = module_extension(
    implementation = lambda _: _prolead_repos(),
)
