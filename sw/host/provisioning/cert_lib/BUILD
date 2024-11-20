# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "cert_lib",
    srcs = ["src/lib.rs"],
    data = ["//sw/device/silicon_creator/manuf/keys/fake:ext_ca.pem"],
    deps = [
        "//sw/host/opentitanlib",
        "//sw/host/ot_certs",
        "@crate_index//:anyhow",
        "@crate_index//:arrayvec",
        "@crate_index//:elliptic-curve",
        "@crate_index//:hex",
        "@crate_index//:log",
        "@crate_index//:num-bigint-dig",
        "@crate_index//:openssl",
        "@crate_index//:p256",
        "@crate_index//:serde",
    ],
)

rust_test(
    name = "openssl_verify",
    timeout = "short",
    crate = ":cert_lib",
)
