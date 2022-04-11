# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")
load("//third_party/cargo:crates.bzl", "all_crate_deps")

rust_library(
    name = "cryptotest_parser",
    srcs = ["cryptotest_parser.rs"],
    deps = [
        "//third_party/cargo:thiserror",
        "//third_party/cargo:regex",
        "//third_party/cargo:lazy_static",
    ],
)

rust_test(
    name = "cryptotest_parser_test",
    crate = ":cryptotest_parser",
)
