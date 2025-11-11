# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def _lowrisc_repos():
    VERSION = "20251111-1"
    http_archive(
        name = "lowrisc_rv32imcb_toolchain",
        url = "https://github.com/lowRISC/lowrisc-toolchains/releases/download/{v}/lowrisc-toolchain-rv32imcb-x86_64-{v}.tar.xz".format(v = VERSION),
        sha256 = "42be8b4a7e2fe8ea9274759c8574eb3b763a5072741a75d22189c93b149b6fab",
        strip_prefix = "lowrisc-toolchain-rv32imcb-x86_64-{}".format(VERSION),
        build_file = ":BUILD.lowrisc_rv32imcb_toolchain.bazel",
    )

lowrisc_rv32imcb_toolchain = module_extension(
    implementation = lambda _: _lowrisc_repos(),
)
