# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def _lowrisc_repos():
    VERSION = "20250710-1"
    http_archive(
        name = "lowrisc_rv32imcb_toolchain",
        url = "https://github.com/lowRISC/lowrisc-toolchains/releases/download/{v}/lowrisc-toolchain-rv32imcb-x86_64-{v}.tar.xz".format(v = VERSION),
        sha256 = "6f02aae27c097c71a2875a215896a0301e32ab56d6d26e917dae59d124c573fb",
        strip_prefix = "lowrisc-toolchain-rv32imcb-x86_64-{}".format(VERSION),
        build_file = ":BUILD.lowrisc_rv32imcb_toolchain.bazel",
    )

lowrisc_rv32imcb_toolchain = module_extension(
    implementation = lambda _: _lowrisc_repos(),
)
