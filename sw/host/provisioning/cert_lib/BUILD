# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")
load("@bazel_skylib//rules:common_settings.bzl", "bool_flag")

package(default_visibility = ["//visibility:public"])

bool_flag(
    name = "enable_mldsa_signing_for_test",
    build_setting_default = False,
)

config_setting(
    name = "mldsa_signing_for_test",
    flag_values = {":enable_mldsa_signing_for_test": "True"},
)

rust_library(
    name = "cert_lib",
    srcs = ["src/lib.rs"],
    crate_features = select({
        ":mldsa_signing_for_test": ["mldsa_experimental_signing"],
        "//conditions:default": [],
    }),
    data = [
        "//sw/device/silicon_creator/manuf/keys/fake:ext_ca.pem",
        "@openssl",
    ],
    edition = "2024",
    deps = [
        "//sw/host/opentitanlib",
        "//sw/host/ot_certs",
        "@crate_index//:anyhow",
        "@crate_index//:arrayvec",
        "@crate_index//:base64ct",
        "@crate_index//:elliptic-curve",
        "@crate_index//:hex",
        "@crate_index//:log",
        "@crate_index//:ml-dsa",
        "@crate_index//:num-bigint-dig",
        "@crate_index//:openssl",
        "@crate_index//:p256",
        "@crate_index//:serde",
        "@hwtrust",
        "@rules_rust//rust/runfiles",
    ],
)

rust_test(
    name = "openssl_verify",
    timeout = "short",
    crate = ":cert_lib",
    edition = "2024",
)
