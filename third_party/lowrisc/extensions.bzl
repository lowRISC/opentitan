# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def _lowrisc_repos():
    VERSION = "20260224-1"
    http_archive(
        name = "lowrisc_rv32imcb_toolchain",
        url = "https://storage.googleapis.com/lowrisc-ci-longterm-cache/lowrisc-toolchain-rv32imcb-x86_64-cheriot.tar.xz",
        sha256 = "55726c473177b3a6428e430c9cbb031f474680f5776a7565caec75c98d0ffdbd",
        strip_prefix = "lowrisc-toolchain-rv32imcb-x86_64-",
        build_file = ":BUILD.lowrisc_rv32imcb_toolchain.bazel",
    )

lowrisc_rv32imcb_toolchain = module_extension(
    implementation = lambda _: _lowrisc_repos(),
)
