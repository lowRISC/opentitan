# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

rust_library(
    name = "cryptotest_parser",
    srcs = ["cryptotest_parser.rs"],
    deps = [
        "//third_party/rust/crates:lazy_static",
        "//third_party/rust/crates:regex",
        "//third_party/rust/crates:thiserror",
    ],
)

rust_test(
    name = "cryptotest_parser_test",
    crate = ":cryptotest_parser",
)
