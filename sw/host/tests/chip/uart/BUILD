# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "uart_tx_rx",
    srcs = [
        "src/uart_tx_rx.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "//third_party/rust/crates:anyhow",
        "//third_party/rust/crates:clap",
        "//third_party/rust/crates:humantime",
        "//third_party/rust/crates:log",
        "//third_party/rust/crates:object",
    ],
)

rust_binary(
    name = "uart_baud_rate",
    srcs = [
        "src/uart_baud_rate.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "//third_party/rust/crates:anyhow",
        "//third_party/rust/crates:clap",
        "//third_party/rust/crates:humantime",
        "//third_party/rust/crates:log",
        "//third_party/rust/crates:object",
    ],
)

rust_binary(
    name = "uart_loopback",
    srcs = [
        "src/uart_loopback.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "//third_party/rust/crates:anyhow",
        "//third_party/rust/crates:clap",
        "//third_party/rust/crates:humantime",
        "//third_party/rust/crates:log",
        "//third_party/rust/crates:object",
    ],
)
