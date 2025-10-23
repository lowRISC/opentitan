# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

system_libs = module_extension(
    implementation = lambda _: _system_libs_repos(),
)

def _system_libs_repos():
    http_archive(
        name = "libudev_zero",
        build_file = Label("//third_party/system_libs:BUILD.libudev_zero.bazel"),
        url = "https://github.com/illiliti/libudev-zero/archive/refs/tags/1.0.3.tar.gz",
        strip_prefix = "libudev-zero-1.0.3",
        sha256 = "0bd89b657d62d019598e6c7ed726ff8fed80e8ba092a83b484d66afb80b77da5",
    )
