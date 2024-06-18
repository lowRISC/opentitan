# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//bindgen:defs.bzl", "rust_bindgen_library")
load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(default_visibility = ["//visibility:public"])

# NOTE: By convention, the bindgen crate name and the preprocessor NAMESPACE
# value need to contain the same algorithm variant name, as:
#
# - bindgen_${variant}
# - NAMESPACE=SPX_${variant}_
#
# The rust wrapper in the `spincsplus` library below depends on being able to
# use token pasting to create symbol paths to the low-level C variables and
# functions.
rust_bindgen_library(
    name = "bindgen_shake_128s_simple",
    bindgen_flags = [
        "--allowlist-function=SPX_.*",
        "--allowlist-var=CRYPTO_.*",
        "--allowlist-var=SPX_.*",
    ],
    cc_lib = "@sphincsplus_fips205_ipd//:sphincs_random_shake_128s_simple",
    clang_flags = [
        "-DPARAMS=sphincs-shake-128s",
        "-DNAMESPACE=SPX_shake_128s_simple_",
    ],
    header = "@sphincsplus_fips205_ipd//:api.h",
)

rust_bindgen_library(
    name = "bindgen_sha2_128s_simple",
    bindgen_flags = [
        "--allowlist-function=SPX_.*",
        "--allowlist-var=CRYPTO_.*",
        "--allowlist-var=SPX_.*",
    ],
    cc_lib = "@sphincsplus_fips205_ipd//:sphincs_random_sha2_128s_simple",
    clang_flags = [
        "-DPARAMS=sphincs-sha2-128s",
        "-DNAMESPACE=SPX_sha2_128s_simple_",
    ],
    header = "@sphincsplus_fips205_ipd//:api.h",
)

rust_library(
    name = "sphincsplus",
    srcs = [
        "error.rs",
        "key.rs",
        "lib.rs",
        "variants.rs",
    ],
    proc_macro_deps = [
        "@crate_index//:paste",
    ],
    deps = [
        ":bindgen_sha2_128s_simple",
        ":bindgen_shake_128s_simple",
        "@crate_index//:pem-rfc7468",
        "@crate_index//:strum",
        "@crate_index//:thiserror",
    ],
)

rust_test(
    name = "sphincsplus_test",
    crate = ":sphincsplus",
)
