# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "spi_device_ottf_console",
    srcs = [
        "src/main.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "//third_party/rust/crates:anyhow",
        "//third_party/rust/crates:clap",
        "//third_party/rust/crates:humantime",
        "//third_party/rust/crates:log",
        "//third_party/rust/crates:regex",
    ],
)
