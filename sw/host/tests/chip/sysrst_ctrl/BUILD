# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "sysrst_ctrl",
    srcs = [
        "mod.rs",
        "sysrst_ctrl.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:log",
    ],
)

rust_binary(
    name = "sysrst_ctrl_inputs",
    srcs = [
        "sysrst_ctrl_inputs.rs",
    ],
    deps = [
        ":sysrst_ctrl",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:object",
        "@crate_index//:once_cell",
        "@crate_index//:serde_json",
    ],
)

rust_binary(
    name = "sysrst_ctrl_outputs",
    srcs = [
        "sysrst_ctrl_outputs.rs",
    ],
    deps = [
        ":sysrst_ctrl",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:object",
        "@crate_index//:once_cell",
        "@crate_index//:serde_json",
    ],
)

rust_binary(
    name = "sysrst_ctrl_in_irq",
    srcs = [
        "sysrst_ctrl_in_irq.rs",
    ],
    deps = [
        ":sysrst_ctrl",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:object",
        "@crate_index//:once_cell",
        "@crate_index//:serde_json",
    ],
)

rust_binary(
    name = "sysrst_ctrl_ulp_z3_wakeup",
    srcs = [
        "sysrst_ctrl_ulp_z3_wakeup.rs",
    ],
    deps = [
        ":sysrst_ctrl",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:object",
        "@crate_index//:once_cell",
        "@crate_index//:serde_json",
    ],
)

rust_binary(
    name = "sysrst_ctrl_ec_rst_l",
    srcs = [
        "sysrst_ctrl_ec_rst_l.rs",
    ],
    deps = [
        ":sysrst_ctrl",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:object",
        "@crate_index//:once_cell",
        "@crate_index//:serde_json",
    ],
)

rust_binary(
    name = "sysrst_ctrl_reset",
    srcs = [
        "sysrst_ctrl_reset.rs",
    ],
    deps = [
        ":sysrst_ctrl",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:object",
        "@crate_index//:once_cell",
        "@crate_index//:serde_json",
    ],
)
