# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "jtag",
    srcs = [
        "src/jtag.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:log",
    ],
)

rust_binary(
    name = "jtag_tap_sel",
    srcs = [
        "src/jtag_tap_sel.rs",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen/chip:top_earlgrey",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:log",
        "@crate_index//:once_cell",
        "@crate_index//:regex",
    ],
)

rust_binary(
    name = "lc_disabled",
    srcs = [
        "src/lc_disabled.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:log",
        "@crate_index//:rand",
    ],
)
