# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "opentitansession",
    srcs = ["src/main.rs"],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:directories",
        "@crate_index//:env_logger",
        "@crate_index//:erased-serde",
        "@crate_index//:hex",
        "@crate_index//:indicatif",
        "@crate_index//:log",
        "@crate_index//:regex",
        "@crate_index//:rustix",
        "@crate_index//:serde",
        "@crate_index//:serde_json",
        "@crate_index//:shellwords",
        "@crate_index//:thiserror",
    ],
)
