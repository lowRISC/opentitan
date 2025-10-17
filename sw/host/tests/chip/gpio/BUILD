# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "gpio_pinmux",
    srcs = [
        "src/gpio_pinmux.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "//sw/host/ot_hal",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:serde_json",
    ],
)

rust_binary(
    name = "gpio_intr",
    srcs = [
        "src/gpio_intr.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "//sw/host/ot_hal",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:serde_json",
    ],
)

rust_binary(
    name = "sleep_pin_mio_dio_val",
    srcs = [
        "src/sleep_pin_mio_dio_val.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:serde_json",
    ],
)

rust_binary(
    name = "sleep_pin_retention",
    srcs = [
        "src/sleep_pin_retention.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:serde_json",
    ],
)

rust_binary(
    name = "sleep_pin_wake",
    srcs = [
        "src/sleep_pin_wake.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:object",
        "@crate_index//:rand",
    ],
)
