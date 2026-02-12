# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_doc", "rust_library", "rust_test")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "proto",
    srcs = [
        "src/lib.rs",
    ],
    crate_name = "ot_proxy_proto",
    deps = [
        "//sw/host/opentitanlib:opentitanlib_base",
        "@crate_index//:serde",
    ],
)

rust_doc(
    name = "proto_doc",
    crate = ":proto",
)

rust_test(
    name = "proto_test",
    crate = ":proto",
)
