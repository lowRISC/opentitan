# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_library")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "util_lib",
    srcs = [
        "src/lib.rs",
        "src/response.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "//sw/host/ot_hal",
        "//sw/host/provisioning/cert_lib",
        "@crate_index//:anyhow",
        "@crate_index//:arrayvec",
        "@crate_index//:hex",
        "@crate_index//:indexmap",
        "@crate_index//:rand",
        "@crate_index//:rsa",
        "@crate_index//:serde",
        "@crate_index//:tiny-keccak",
        "@crate_index//:zerocopy",
    ],
)
