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
        sha256 = "a7a4c18d0d5609b26f3341dc7a9dd6829174d542ee6f0434f5fa7319e0811b75",
        strip_prefix = "wycheproof-snapshot-d9f6ec7d8bd8c96da05368999094e4a75ba5cb3d",
        url = "https://github.com/lowRISC/wycheproof/archive/refs/tags/snapshot-d9f6ec7d8bd8c96da05368999094e4a75ba5cb3d.tar.gz",
    )
