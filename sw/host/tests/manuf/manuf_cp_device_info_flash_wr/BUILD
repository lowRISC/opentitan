# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "manuf_cp_device_info_flash_wr",
    srcs = [
        "src/main.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:regex",
        "@crate_index//:structopt",
    ],
)

py_binary(
    name = "gen_test_exit_token",
    srcs = [
        "gen_test_exit_token.py",
    ],
)
