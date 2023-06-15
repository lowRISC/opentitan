# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")
load("//rules:lc.bzl", "lc_raw_unlock_token")

package(default_visibility = ["//visibility:public"])

lc_raw_unlock_token(
    name = "lc_raw_unlock_token",
)

rust_binary(
    name = "manuf_cp_unlock_raw",
    srcs = [
        "src/main.rs",
        ":lc_raw_unlock_token",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
    ],
)
