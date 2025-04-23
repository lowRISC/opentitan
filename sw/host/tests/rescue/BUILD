# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")
load("//rules:ujson.bzl", "ujson_rust")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "xmodem_protocol",
    srcs = ["xmodem_protocol.rs"],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:rustix",
    ],
)

rust_binary(
    name = "usbdfu_protocol",
    srcs = ["usbdfu_protocol.rs"],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
    ],
)
