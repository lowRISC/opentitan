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
    data = [
        "//sw/device/silicon_creator/manuf/keys/fake:dice_mldsa_ca.pem",
        "//sw/device/silicon_creator/manuf/keys/fake:ext_ca.pem",
        "//sw/device/silicon_creator/manuf/keys/fake:sk_mldsa.pkcs8.der",
        "//sw/host/hsmtool",
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
        "@crate_index//:num-bigint-dig",
        "@crate_index//:openssl",
        "@crate_index//:p256",
        "@crate_index//:serde",
        "@crate_index//:serde_json",
        "@crate_index//:tempfile",
        "@crate_index//:zeroize",
        "@hwtrust",
        "@rules_rust//rust/runfiles",
    ],
)

rust_test(
    name = "openssl_verify",
    timeout = "short",
    crate = ":cert_lib",
    data = [
        "//signing/softhsm",
        "@softhsm2//:gen_dir",
    ],
    edition = "2024",
    env = {
        "HSMTOOL_MODULE": "$(rootpath @softhsm2//:gen_dir)/lib/softhsm/libsofthsm2.so",
    },
)
