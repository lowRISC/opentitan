# Copyright lowRISC contributors.
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
        "//third_party/rust/crates:anyhow",
        "//third_party/rust/crates:clap",
        "//third_party/rust/crates:humantime",
        "//third_party/rust/crates:log",
        "//third_party/rust/crates:num_enum",
        "//third_party/rust/crates:regex",
    ],
)

rust_test(
    name = "e2e_bootstrap_rma_test",
    srcs = [
        "src/main.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "//third_party/rust/crates:anyhow",
        "//third_party/rust/crates:clap",
        "//third_party/rust/crates:humantime",
        "//third_party/rust/crates:log",
        "//third_party/rust/crates:num_enum",
        "//third_party/rust/crates:regex",
    ],
)

py_binary(
    name = "gen_rma_token",
    srcs = [
        "gen_rma_token.py",
    ],
)
