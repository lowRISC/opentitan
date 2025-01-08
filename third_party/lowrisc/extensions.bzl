# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def _lowrisc_repos():
    VERSION = "20240923-1"
    http_archive(
        name = "lowrisc_rv32imcb_toolchain",
        url = "https://github.com/lowRISC/lowrisc-toolchains/releases/download/{v}/lowrisc-toolchain-rv32imcb-{v}.tar.xz".format(v = VERSION),
        sha256 = "aeea1983553f4c81c6409abcf0d6ca33b5ed4716b2b694e7ff030523cf13486a",
        strip_prefix = "lowrisc-toolchain-rv32imcb-{}".format(VERSION),
        build_file = ":BUILD.lowrisc_rv32imcb_toolchain.bazel",
    )

lowrisc_rv32imcb_toolchain = module_extension(
    implementation = lambda _: _lowrisc_repos(),
)
