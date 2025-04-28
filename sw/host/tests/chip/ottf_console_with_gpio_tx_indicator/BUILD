# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "ottf_console_with_gpio_tx_indicator",
    srcs = [
        "src/main.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "//sw/host/provisioning/ujson_lib",
        "//third_party/rust/crates:anyhow",
        "//third_party/rust/crates:clap",
        "//third_party/rust/crates:humantime",
        "//third_party/rust/crates:log",
        "@crate_index//:object",
    ],
)
