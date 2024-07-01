# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:ujson.bzl", "ujson_rust")
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")

package(default_visibility = ["//visibility:public"])

ujson_rust(
    name = "commands_rust",
    srcs = ["//sw/device/tests/crypto/cryptotest/json:commands"],
)

ujson_rust(
    name = "aes_commands_rust",
    srcs = ["//sw/device/tests/crypto/cryptotest/json:aes_commands"],
)

ujson_rust(
    name = "drbg_commands_rust",
    srcs = ["//sw/device/tests/crypto/cryptotest/json:drbg_commands"],
)

ujson_rust(
    name = "hash_commands_rust",
    srcs = ["//sw/device/tests/crypto/cryptotest/json:hash_commands"],
)

ujson_rust(
    name = "ecdh_commands_rust",
    srcs = ["//sw/device/tests/crypto/cryptotest/json:ecdh_commands"],
)

ujson_rust(
    name = "ecdsa_commands_rust",
    srcs = ["//sw/device/tests/crypto/cryptotest/json:ecdsa_commands"],
)

ujson_rust(
    name = "hmac_commands_rust",
    srcs = ["//sw/device/tests/crypto/cryptotest/json:hmac_commands"],
)

ujson_rust(
    name = "kmac_commands_rust",
    srcs = ["//sw/device/tests/crypto/cryptotest/json:kmac_commands"],
)

ujson_rust(
    name = "sphincsplus_commands_rust",
    srcs = ["//sw/device/tests/crypto/cryptotest/json:sphincsplus_commands"],
)

rust_library(
    name = "cryptotest_commands",
    srcs = [
        "src/aes_commands.rs",
        "src/commands.rs",
        "src/drbg_commands.rs",
        "src/ecdh_commands.rs",
        "src/ecdsa_commands.rs",
        "src/hash_commands.rs",
        "src/hmac_commands.rs",
        "src/kmac_commands.rs",
        "src/lib.rs",
        "src/sphincsplus_commands.rs",
    ],
    compile_data = [
        ":commands_rust",
        ":aes_commands_rust",
        ":ecdh_commands_rust",
        ":drbg_commands_rust",
        ":ecdsa_commands_rust",
        ":hash_commands_rust",
        ":hmac_commands_rust",
        ":kmac_commands_rust",
        ":sphincsplus_commands_rust",
    ],
    rustc_env = {
        "commands_loc": "$(execpath :commands_rust)",
        "aes_commands_loc": "$(execpath :aes_commands_rust)",
        "ecdh_commands_loc": "$(execpath :ecdh_commands_rust)",
        "drbg_commands_loc": "$(execpath :drbg_commands_rust)",
        "ecdsa_commands_loc": "$(execpath :ecdsa_commands_rust)",
        "hash_commands_loc": "$(execpath :hash_commands_rust)",
        "hmac_commands_loc": "$(execpath :hmac_commands_rust)",
        "kmac_commands_loc": "$(execpath :kmac_commands_rust)",
        "sphincsplus_commands_loc": "$(execpath :sphincsplus_commands_rust)",
    },
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:arrayvec",
        "@crate_index//:serde",
    ],
)
