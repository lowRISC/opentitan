# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_doc", "rust_library")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "ot_certs",
    srcs = [
        "src/lib.rs",
        "src/template/hjson.rs",
        "src/template/mod.rs",
    ],
    deps = [
        "@crate_index//:anyhow",
        "@crate_index//:deser-hjson",
        "@crate_index//:hex",
        "@crate_index//:num-bigint-dig",
        "@crate_index//:num-traits",
        "@crate_index//:serde",
        "@crate_index//:serde_with",
        "@crate_index//:strum",
    ],
)

rust_doc(
    name = "ot_certs_doc",
    crate = ":ot_certs",
)
