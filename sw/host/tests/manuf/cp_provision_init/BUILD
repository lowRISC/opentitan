# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")
load("//rules:ujson.bzl", "ujson_rust")
load("//rules:lc.bzl", "lc_raw_unlock_token")

package(default_visibility = ["//visibility:public"])

lc_raw_unlock_token(
    name = "lc_raw_unlock_token",
)

ujson_rust(
    name = "provisioning_data",
    srcs = ["//sw/device/lib/testing/json:provisioning_data"],
)

rust_binary(
    name = "cp_provision_init",
    srcs = [
        "src/main.rs",
        "src/provisioning_data.rs",
        ":lc_raw_unlock_token",
    ],
    compile_data = [":provisioning_data"],
    rustc_env = {
        "provisioning_data": "$(location :provisioning_data)",
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
