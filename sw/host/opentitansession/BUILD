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
        "//third_party/rust/crates:anyhow",
        "//third_party/rust/crates:directories",
        "//third_party/rust/crates:env_logger",
        "//third_party/rust/crates:erased_serde",
        "//third_party/rust/crates:hex",
        "//third_party/rust/crates:indicatif",
        "//third_party/rust/crates:log",
        "//third_party/rust/crates:nix",
        "//third_party/rust/crates:raw_tty",
        "//third_party/rust/crates:regex",
        "//third_party/rust/crates:serde",
        "//third_party/rust/crates:serde_json",
        "//third_party/rust/crates:shellwords",
        "//third_party/rust/crates:structopt",
        "//third_party/rust/crates:thiserror",
    ],
)
