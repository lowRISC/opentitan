# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")
load("@rules_rust//proto/prost:defs.bzl", "rust_prost_library")

rust_prost_library(
    name = "spawn_rs_proto",
    proto = "//third_party/bazel:spawn_proto",
)

rust_library(
    name = "exec_log_lib",
    srcs = [
        "src/bazel_exec_log.rs",
        "src/exec_log.rs",
        "src/lib.rs",
    ],
    deps = [
        ":spawn_rs_proto",
        "@crate_index//:anyhow",
        "@crate_index//:bytes",
        "@crate_index//:log",
        "@crate_index//:prost",
        "@crate_index//:serde",
    ],
)

rust_binary(
    name = "exec_log",
    srcs = [
        "src/main.rs",
    ],
    deps = [
        ":exec_log_lib",
        ":spawn_rs_proto",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:once_cell",
        "@crate_index//:serde_json",
    ],
)
