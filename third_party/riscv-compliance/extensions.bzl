# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

riscv_compliance = module_extension(
    implementation = lambda _: _riscv_compliance_repos(),
)

def _riscv_compliance_repos():
    http_archive(
        name = "riscv-compliance",
        build_file = Label("//third_party/riscv-compliance:BUILD.riscv-compliance.bazel"),
        sha256 = "e77d823189c145314e48d4c29bcecc844b9c1582826ff406ec499cad7e95d0e4",
        strip_prefix = "riscv-arch-test-2636302c27557b42d99bed7e0537beffdf8e1ab4",
        urls = [
            "https://github.com/riscv/riscv-compliance/archive/2636302c27557b42d99bed7e0537beffdf8e1ab4.tar.gz",
        ],
        patches = [
            Label("//third_party/riscv-compliance/patches:0001-Add-configurable-trap-alignment-and-entry-point-to-p.patch"),
        ],
        patch_args = ["-p1"],
    )
