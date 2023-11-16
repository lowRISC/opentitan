# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_doc", "rust_library", "rust_test")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "ot_certs",
    srcs = [
        "src/lib.rs",
        "src/offsets.rs",
        "src/template/hjson.rs",
        "src/template/mod.rs",
        "src/types.rs",
        "src/x509.rs",
        "src/x509/extension.rs",
    ],
    proc_macro_deps = [
        "@crate_index//:indoc",
    ],
    deps = [
        "@crate_index//:anyhow",
        "@crate_index//:asn1",
        "@crate_index//:deser-hjson",
        "@crate_index//:hex",
        "@crate_index//:log",
        "@crate_index//:memchr",
        "@crate_index//:num-bigint-dig",
        "@crate_index//:num-traits",
        "@crate_index//:openssl",
        "@crate_index//:rand",
        "@crate_index//:serde",
        "@crate_index//:serde_with",
        "@crate_index//:strum",
    ],
)

rust_test(
    name = "ot_certs_test",
    crate = ":ot_certs",
    proc_macro_deps = [
        "@crate_index//:indoc",
    ],
)

rust_doc(
    name = "ot_certs_doc",
    crate = ":ot_certs",
)
