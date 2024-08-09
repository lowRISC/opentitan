# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")
load("@rules_rust//bindgen:defs.bzl", "rust_bindgen_library")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "acorn",
    srcs = [
        "acorn.rs",
        "lib.rs",
    ],
    crate_root = "lib.rs",
    deps = [
        "//sw/host/hsmtool/acorn/vendor:acorn_bindgen",
        "@crate_index//:anyhow",
        "@crate_index//:bitflags",
        "@crate_index//:libloading",
        "@crate_index//:thiserror",
    ],
)
