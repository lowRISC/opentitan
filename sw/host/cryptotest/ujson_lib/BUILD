# Copyright lowRISC contributors.
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

rust_library(
    name = "cryptotest_commands",
    srcs = [
        "src/aes_commands.rs",
        "src/commands.rs",
        "src/lib.rs",
    ],
    compile_data = [
        ":commands_rust",
        ":aes_commands_rust",
    ],
    rustc_env = {
        "commands_loc": "$(execpath :commands_rust)",
        "aes_commands_loc": "$(execpath :aes_commands_rust)",
    },
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:arrayvec",
        "@crate_index//:serde",
    ],
)
