# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_library")
load("//rules:lc.bzl", "lc_raw_unlock_token")
load("//rules:ujson.bzl", "ujson_rust")

package(default_visibility = ["//visibility:public"])

lc_raw_unlock_token(
    name = "lc_raw_unlock_token",
)

ujson_rust(
    name = "provisioning_command",
    srcs = ["//sw/device/lib/testing/json:provisioning_command"],
)

ujson_rust(
    name = "provisioning_data",
    srcs = ["//sw/device/lib/testing/json:provisioning_data"],
)

rust_library(
    name = "cp_lib",
    srcs = [
        "src/lib.rs",
        "src/provisioning_command.rs",
        "src/provisioning_data.rs",
        ":lc_raw_unlock_token",
    ],
    compile_data = [
        ":provisioning_command",
        ":provisioning_data",
    ],
    rustc_env = {
        "provisioning_command": "$(location :provisioning_command)",
        "provisioning_data": "$(location :provisioning_data)",
    },
    deps = [
        "//sw/host/opentitanlib",
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
