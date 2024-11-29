# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "usb",
    srcs = [
        "mod.rs",
        "usb.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:log",
        "@crate_index//:rusb",
    ],
)

rust_binary(
    name = "usbdev_aon_wake",
    srcs = [
        "usbdev_aon_wake.rs",
    ],
    deps = [
        ":usb",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:rusb",
    ],
)

rust_binary(
    name = "usb_harness",
    srcs = [
        "usb_harness.rs",
    ],
    deps = [
        ":usb",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
    ],
)

rust_binary(
    name = "usbdev_smoketest",
    srcs = [
        "usbdev_smoketest.rs",
    ],
    deps = [
        ":usb",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:rusb",
        "@crate_index//:serialport",
    ],
)
