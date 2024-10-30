# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_doc", "rust_library", "rust_test", "rust_test_suite")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "generic_cert",
    srcs = ["tests/generic.hjson"],
)

filegroup(
    name = "example_cert",
    srcs = ["tests/example.hjson"],
)

filegroup(
    name = "example_data",
    srcs = ["tests/example_data.json"],
)

rust_library(
    name = "ot_certs",
    srcs = [
        "src/asn1/builder.rs",
        "src/asn1/codegen.rs",
        "src/asn1/der.rs",
        "src/asn1/dice_tcb.rs",
        "src/asn1/mod.rs",
        "src/asn1/x509.rs",
        "src/codegen.rs",
        "src/lib.rs",
        "src/template/mod.rs",
        "src/template/subst.rs",
        "src/template/testgen.rs",
        "src/x509.rs",
        "src/x509/extension.rs",
    ],
    proc_macro_deps = [
        "@crate_index//:indoc",
    ],
    deps = [
        "@crate_index//:anyhow",
        "@crate_index//:asn1",
        "@crate_index//:clap",
        "@crate_index//:deser-hjson",
        "@crate_index//:heck",
        "@crate_index//:hex",
        "@crate_index//:indexmap",
        "@crate_index//:log",
        "@crate_index//:memchr",
        "@crate_index//:num-bigint-dig",
        "@crate_index//:num-traits",
        "@crate_index//:openssl",
        "@crate_index//:rand",
        "@crate_index//:serde",
        "@crate_index//:serde_json",
        "@crate_index//:strum",
        # We need those because they are not re-exported by openssl
        # This can be fixed when https://github.com/sfackler/rust-openssl/pull/2021
        # is merged.
        "@crate_index//:openssl-sys",
        "@crate_index//:foreign-types",
    ],
)

rust_test(
    name = "ot_certs_test",
    crate = ":ot_certs",
    proc_macro_deps = [
        "@crate_index//:indoc",
    ],
    deps = [
        "@crate_index//:base64ct",
    ],
)

rust_test_suite(
    name = "ot_certs_e2e_test",
    srcs = glob(["tests/*.rs"]),
    compile_data = [
        ":generic_cert",
        ":example_cert",
        ":example_data",
    ],
    deps = [
        ":ot_certs",
        "@crate_index//:anyhow",
        "@crate_index//:base64ct",
        "@crate_index//:num-bigint-dig",
        "@crate_index//:num-traits",
    ],
)

rust_doc(
    name = "ot_certs_doc",
    crate = ":ot_certs",
)
