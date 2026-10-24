# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "mldsa",
    srcs = [
        "error.rs",
        "key.rs",
        "lib.rs",
        "variants.rs",
    ],
    deps = [
        "@crate_index//:ml-dsa",
        "@crate_index//:pkcs8",
        "@crate_index//:strum",
        "@crate_index//:thiserror",
        "@crate_index//:zeroize",
    ],
)

rust_test(
    name = "mldsa_test",
    compile_data = glob(["testdata/**"]),
    crate = ":mldsa",
)
