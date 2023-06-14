# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

rust_library(
    name = "cryptotest_parser",
    srcs = ["cryptotest_parser.rs"],
    deps = [
        "@crate_index//:once_cell",
        "@crate_index//:regex",
        "@crate_index//:thiserror",
    ],
)

rust_test(
    name = "cryptotest_parser_test",
    crate = ":cryptotest_parser",
)
