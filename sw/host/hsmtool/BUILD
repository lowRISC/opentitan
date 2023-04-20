# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_doc", "rust_library", "rust_test")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "hsmlib",
    srcs = [
        "src/lib.rs",
        "src/util/attribute/attr.rs",
        "src/util/attribute/attribute_type.rs",
        "src/util/attribute/certificate_type.rs",
        "src/util/attribute/data.rs",
        "src/util/attribute/date.rs",
        "src/util/attribute/error.rs",
        "src/util/attribute/key_type.rs",
        "src/util/attribute/mechanism_type.rs",
        "src/util/attribute/mod.rs",
        "src/util/attribute/object_class.rs",
        "src/util/escape.rs",
        "src/util/mod.rs",
    ],
    crate_name = "hsmtool",
    proc_macro_deps = [
        "@crate_index//:serde_derive",
    ],
    deps = [
        "@crate_index//:anyhow",
        "@crate_index//:cryptoki",
        "@crate_index//:cryptoki-sys",
        "@crate_index//:indexmap",
        "@crate_index//:num_enum",
        "@crate_index//:once_cell",
        "@crate_index//:regex",
        "@crate_index//:serde",
        "@crate_index//:serde_json",
        "@crate_index//:strum",
        "@crate_index//:thiserror",
    ],
)

rust_test(
    name = "hsmlib_test",
    crate = ":hsmlib",
)

rust_doc(
    name = "hsmlib_doc",
    crate = ":hsmlib",
)
