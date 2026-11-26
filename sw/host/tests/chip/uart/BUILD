# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "test_uarts",
    srcs = [
        "src/test_uarts.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
    ],
)

rust_binary(
    name = "uart_tx_rx",
    srcs = [
        "src/uart_tx_rx.rs",
    ],
    deps = [
        ":test_uarts",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:object",
        "@crate_index//:serialport",
    ],
)

rust_binary(
    name = "uart_baud_rate",
    srcs = [
        "src/uart_baud_rate.rs",
    ],
    deps = [
        ":test_uarts",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:object",
    ],
)

rust_binary(
    name = "uart_loopback",
    srcs = [
        "src/uart_loopback.rs",
    ],
    deps = [
        ":test_uarts",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:object",
    ],
)

rust_binary(
    name = "uart_parity_break",
    srcs = [
        "src/uart_parity_break.rs",
    ],
    deps = [
        ":test_uarts",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:object",
    ],
)
