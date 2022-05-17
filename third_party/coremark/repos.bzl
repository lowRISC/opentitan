# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def coremark_repos():
    http_archive(
        name = "coremark",
        build_file = Label("//third_party/coremark:BUILD.coremark.bazel"),
        sha256 = "7a88428bd0777e70d9fef7dad0d61faf52a53bd642b82fd029c8a63934ff6de4",
        strip_prefix = "coremark-21d473aae1f11d52ea592a8685734be2209aa66f",
        urls = [
            "https://github.com/eembc/coremark/archive/21d473aae1f11d52ea592a8685734be2209aa66f.tar.gz",
        ],
        patches = [
            Label("//third_party/coremark:use_ottf_main.patch"),
        ],
        patch_args = ["-p1"],
    )
