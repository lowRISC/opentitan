# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def _sv2v_repos():
    http_archive(
        name = "sv2v",
        build_file_content = """
package(default_visibility = ["//visibility:public"])
filegroup(
    name = "sv2v_bin",
    srcs = ["sv2v"],
)
""",
        urls = ["https://github.com/zachjs/sv2v/releases/download/v0.0.11/sv2v-Linux.zip"],
        strip_prefix = "sv2v-Linux",
        integrity = "sha256-3pUZPZi+a7icBZMlEXAXxvW5Ur/4G7ewwfbgkur3wiA=",
    )

sv2v = module_extension(
    implementation = lambda _: _sv2v_repos(),
)
