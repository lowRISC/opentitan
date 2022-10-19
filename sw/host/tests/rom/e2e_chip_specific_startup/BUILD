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
        "//third_party/rust/crates:anyhow",
        "//third_party/rust/crates:humantime",
        "//third_party/rust/crates:log",
        "//third_party/rust/crates:serde",
        "//third_party/rust/crates:serde_json",
        "//third_party/rust/crates:structopt",
    ],
)
