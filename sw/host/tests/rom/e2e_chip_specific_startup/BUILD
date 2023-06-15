# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")
load("//rules:ujson.bzl", "ujson_rust")

package(default_visibility = ["//visibility:public"])

ujson_rust(
    name = "chip_specific_startup",
    srcs = ["//sw/device/lib/testing/json:chip_specific_startup"],
)

rust_binary(
    name = "e2e_chip_specific_startup",
    srcs = [
        "src/chip_specific_startup.rs",
        "src/main.rs",
    ],
    compile_data = [":chip_specific_startup"],
    rustc_env = {
        "chip_specific_startup": "$(location :chip_specific_startup)",
    },
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:arrayvec",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:serde",
        "@crate_index//:serde_json",
    ],
)
