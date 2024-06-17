# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//bindgen:defs.bzl", "rust_bindgen_library")
load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(default_visibility = ["//visibility:public"])

rust_bindgen_library(
    name = "sphincsplus_bindgen",
    bindgen_flags = [
        "--allowlist-function=crypto_.*",
        "--allowlist-var=CRYPTO_.*",
        "--allowlist-var=SPX_.*",
    ],
    cc_lib = "@sphincsplus_fips205_ipd//:sphincs_random_sha2_128s_simple",
    clang_flags = ["-DPARAMS=sphincs-sha2-128s"],
    header = "@sphincsplus_fips205_ipd//:api.h",
)

rust_library(
    name = "sphincsplus",
    srcs = ["lib.rs"],
    deps = [
        ":sphincsplus_bindgen",
        "@crate_index//:thiserror",
    ],
)

rust_test(
    name = "sphincsplus_test",
    crate = ":sphincsplus",
)
