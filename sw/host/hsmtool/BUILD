# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_doc", "rust_library", "rust_test")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "hsmlib",
    srcs = [
        "src/commands/mod.rs",
        "src/commands/token.rs",
        "src/error.rs",
        "src/lib.rs",
        "src/module.rs",
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
        "src/util/helper.rs",
        "src/util/key/mod.rs",
        "src/util/key/rsa.rs",
        "src/util/mod.rs",
        "src/util/signing.rs",
    ],
    crate_name = "hsmtool",
    proc_macro_deps = [
        "@crate_index//:serde_derive",
        "@lowrisc_serde_annotate//annotate_derive:annotate_derive",
    ],
    deps = [
        "@crate_index//:anyhow",
        "@crate_index//:atty",
        "@crate_index//:clap",
        "@crate_index//:cryptoki",
        "@crate_index//:cryptoki-sys",
        "@crate_index//:hex",
        "@crate_index//:indexmap",
        "@crate_index//:num_enum",
        "@crate_index//:once_cell",
        "@crate_index//:rand",
        "@crate_index//:regex",
        "@crate_index//:rsa",
        "@crate_index//:serde",
        "@crate_index//:serde_json",
        "@crate_index//:sha2",
        "@crate_index//:strum",
        "@crate_index//:thiserror",
        "@crate_index//:typetag",
        "@lowrisc_serde_annotate//:serde_annotate",
    ],
)

rust_binary(
    name = "hsmtool",
    srcs = ["src/hsmtool.rs"],
    deps = [
        ":hsmlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:cryptoki",
        "@crate_index//:env_logger",
        "@crate_index//:log",
        "@crate_index//:secrecy",
    ],
)

rust_test(
    name = "hsmlib_test",
    crate = ":hsmlib",
    data = glob([
        "src/util/key/testdata/**",
    ]),
)

rust_doc(
    name = "hsmlib_doc",
    crate = ":hsmlib",
)
