# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_proc_macro")

package(default_visibility = ["//visibility:public"])

rust_proc_macro(
    name = "opentitantool_derive",
    srcs = ["src/lib.rs"],
    deps = [
        "@crate_index//:proc-macro2",
        "@crate_index//:quote",
        "@crate_index//:syn",
    ],
)
