# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "ft_lib",
    srcs = ["src/lib.rs"],
    data = ["//sw/device/silicon_creator/manuf/keys/fake:fake_ca.pem"],
    deps = [
        "//sw/host/opentitanlib",
        "//sw/host/ot_certs",
        "//sw/host/provisioning/ujson_lib",
        "@crate_index//:aes",
        "@crate_index//:anyhow",
        "@crate_index//:arrayvec",
        "@crate_index//:clap",
        "@crate_index//:elliptic-curve",
        "@crate_index//:hex",
        "@crate_index//:log",
        "@crate_index//:num-bigint-dig",
        "@crate_index//:p256",
        "@crate_index//:serde",
        "@crate_index//:serde_json",
        "@crate_index//:sha2",
        "@crate_index//:zerocopy",
    ],
)

rust_test(
    name = "openssl_verify",
    timeout = "short",
    crate = ":ft_lib",
)
