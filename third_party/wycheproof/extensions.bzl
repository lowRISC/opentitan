# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

wycheproof = module_extension(
    implementation = lambda _: _wycheproof_repos(),
)

def _wycheproof_repos():
    http_archive(
        name = "wycheproof",
        build_file = Label("//third_party/wycheproof:BUILD.wycheproof_common.bazel"),
        sha256 = "fb3654761053844cea4766db3fcdd41caf8a64a6700040d2bed1d135552911b3",
        strip_prefix = "wycheproof-snapshot-b61843a9a5115bb758134b6a1f5d5e502d445342",
        url = "https://github.com/lowRISC/wycheproof/archive/refs/tags/snapshot-b61843a9a5115bb758134b6a1f5d5e502d445342.tar.gz",
    )
