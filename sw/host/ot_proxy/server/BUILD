# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_doc", "rust_library", "rust_test")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "server",
    srcs = [
        "src/handler.rs",
        "src/lib.rs",
        "src/socket_server.rs",
    ],
    crate_name = "ot_proxy",
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
    name = "server_doc",
    crate = ":server",
)

rust_test(
    name = "server_test",
    crate = ":server",
)
