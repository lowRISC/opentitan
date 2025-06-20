# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

coremark = module_extension(
    implementation = lambda _: _coremark_repos(),
)

def _coremark_repos():
    http_archive(
        name = "coremark",
        build_file = Label("//third_party/coremark:BUILD.coremark.bazel"),
        sha256 = "a5964bf215786d65d08941b6f9a9a4f4e50524f5391fa3826db2994c47d5e7f3",
        strip_prefix = "coremark-eefc986ebd3452d6adde22eafaff3e5c859f29e4",
        urls = [
            "https://github.com/eembc/coremark/archive/eefc986ebd3452d6adde22eafaff3e5c859f29e4.tar.gz",
        ],
        patches = [
            Label("//third_party/coremark/patches:use_ottf_main.patch"),
            Label("//third_party/coremark/patches:print_coremark_per_mhz.patch"),
        ],
        patch_args = ["-p1"],
    )
