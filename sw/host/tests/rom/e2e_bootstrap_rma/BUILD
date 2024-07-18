# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_test")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "e2e_bootstrap_rma",
    srcs = [
        "src/main.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:num_enum",
        "@crate_index//:regex",
    ],
)

rust_test(
    name = "e2e_bootstrap_rma_test",
    srcs = [
        "src/main.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:num_enum",
        "@crate_index//:regex",
    ],
)

py_binary(
    name = "gen_rma_token",
    srcs = [
        "gen_rma_token.py",
    ],
)
