# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "jtag",
    srcs = [
        "src/main.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "//third_party/rust/crates:regex",
        "@crate_index//:anyhow",
        "@crate_index//:humantime",
        "@crate_index//:lazy_static",
        "@crate_index//:log",
        "@crate_index//:serde_json",
        "@crate_index//:structopt",
    ],
)
