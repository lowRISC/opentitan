# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "coverage_lib",
    srcs = ["coverage_lib.rs"],
    data = [
        "//toolchain:opentitan_toolchain",
    ],
    deps = [
        "@crate_index//:anyhow",
        "@crate_index//:byteorder",
        "@crate_index//:hex",
        "@crate_index//:object",
        "@crate_index//:rand",
        "@crate_index//:zerocopy",
        "@rules_rust//rust/runfiles",
    ],
)

rust_binary(
    name = "collect_cc_coverage",
    srcs = ["collect_cc_coverage.rs"],
    deps = [
        ":coverage_lib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
    ],
)

rust_binary(
    name = "generate_coverage_view",
    srcs = ["generate_coverage_view.rs"],
    deps = [
        ":coverage_lib",
        "@crate_index//:addr2line",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:object",
        "@crate_index//:serde",
        "@crate_index//:serde_json",
    ],
)
