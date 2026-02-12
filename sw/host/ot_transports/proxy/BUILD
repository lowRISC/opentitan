# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_doc", "rust_library", "rust_test")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "proxy",
    srcs = [
        "src/emu.rs",
        "src/gpio.rs",
        "src/i2c.rs",
        "src/lib.rs",
        "src/spi.rs",
        "src/uart.rs",
    ],
    crate_name = "ot_transport_proxy",
    deps = [
        "//sw/host/opentitanlib:opentitanlib_base",
        "//sw/host/ot_proxy/proto",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:log",
        "@crate_index//:serde",
        "@crate_index//:serde_json",
        "@crate_index//:thiserror",
        "@crate_index//:tokio",
        "@crate_index//:typetag",
    ],
)

rust_doc(
    name = "proxy_doc",
    crate = ":proxy",
)

rust_test(
    name = "proxy_test",
    crate = ":proxy",
)
