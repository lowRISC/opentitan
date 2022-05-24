# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def riscv_compliance_repos():
    http_archive(
        name = "riscv-compliance",
        build_file = Label("//third_party/riscv-compliance:BUILD.riscv-compliance.bazel"),
        sha256 = "d071d9e5ce07f1cc12fcd7fe6daa87194d0003ddb9cbb40967e98c2374809d07",
        strip_prefix = "riscv-arch-test-5a978cfd444d5e640150d46703deda99057b2bbb",
        urls = [
            "https://github.com/riscv/riscv-compliance/archive/5a978cfd444d5e640150d46703deda99057b2bbb.tar.gz",
        ],
        patches = [
            Label("//third_party/riscv-compliance:0001-Add-configurable-trap-alignment-and-entry-point-to-p.patch"),
        ],
        patch_args = ["-p1"],
    )
