# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def _lowrisc_repos():
    VERSION = "20260224-1"
    http_archive(
        name = "lowrisc_rv32imcb_toolchain",
        url = "https://storage.googleapis.com/lowrisc-ci-longterm-cache/lowrisc-toolchain-rv32imcb.tar.xz",
        sha256 = "a9a578734f5c92541de1a3db0abb24826800a1fa8e76b58bb3b99650d2be752d",
        strip_prefix = "lowrisc-toolchain-rv32imcb-x86_64-",
        build_file = ":BUILD.lowrisc_rv32imcb_toolchain.bazel",
    )

lowrisc_rv32imcb_toolchain = module_extension(
    implementation = lambda _: _lowrisc_repos(),
)
