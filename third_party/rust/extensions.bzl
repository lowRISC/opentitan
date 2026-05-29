# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

serde_annotate = module_extension(
    implementation = lambda _: _serde_annotate_repo(),
)

rust_openssl = module_extension(
    implementation = lambda _: _rust_openssl_repo(),
)

def _serde_annotate_repo():
    http_archive(
        name = "lowrisc_serde_annotate",
        sha256 = "7300ed093fa3de679512ffdab7d0f1824be2b11f499bb852df29c3ae12e1348d",
        strip_prefix = "serde-annotate-0.0.12",
        url = "https://github.com/lowRISC/serde-annotate/archive/refs/tags/v0.0.12.tar.gz",
    )

def _rust_openssl_repo():
    http_archive(
        name = "rust_openssl",
        sha256 = "f928dd655d5738fcc273bd20169d50114e7c8bb179c859e9f4dc7fbb4ef472c9",
        strip_prefix = "rust-openssl-openssl-sys-v0.9.102",
        url = "https://github.com/rust-openssl/rust-openssl/archive/refs/tags/openssl-sys-v0.9.102.tar.gz",
        build_file_content = """
exports_files(
    ["THIRD_PARTY"],
    visibility = ["//visibility:public"],
)
        """,
    )
