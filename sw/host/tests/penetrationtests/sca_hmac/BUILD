# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:ujson.bzl", "ujson_rust")
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "harness",
    srcs = ["src/main.rs"],
    deps = [
        "//sw/host/opentitanlib",
        "//sw/host/penetrationtests/ujson_lib:pentest_commands",
        "//sw/host/tests/penetrationtests/pentest_lib",
        "@crate_index//:anyhow",
        "@crate_index//:arrayvec",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:serde",
        "@crate_index//:serde_json",
    ],
)
