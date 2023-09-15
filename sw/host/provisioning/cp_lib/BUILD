# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_library")
load("//rules:lc.bzl", "lc_raw_unlock_token")

package(default_visibility = ["//visibility:public"])

lc_raw_unlock_token(
    name = "lc_raw_unlock_token",
)

rust_library(
    name = "cp_lib",
    srcs = [
        "src/lib.rs",
        ":lc_raw_unlock_token",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "//sw/host/provisioning/ujson_lib",
        "@crate_index//:anyhow",
        "@crate_index//:arrayvec",
        "@crate_index//:clap",
        "@crate_index//:hex",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:serde",
        "@crate_index//:serde_json",
    ],
)
