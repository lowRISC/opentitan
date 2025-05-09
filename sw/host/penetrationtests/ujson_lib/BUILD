# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:ujson.bzl", "ujson_rust")
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")

package(default_visibility = ["//visibility:public"])

ujson_rust(
    name = "commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:commands"],
)

ujson_rust(
    name = "fi_ibex_commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:ibex_fi_commands"],
)

ujson_rust(
    name = "pentest_lib_commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:pentest_lib_commands"],
)

rust_library(
    name = "pentest_commands",
    srcs = [
        "src/commands.rs",
        "src/fi_ibex_commands.rs",
        "src/lib.rs",
        "src/pentest_lib_commands.rs",
    ],
    compile_data = [
        ":commands_rust",
        ":fi_ibex_commands_rust",
        ":pentest_lib_commands_rust",
    ],
    rustc_env = {
        "commands_loc": "$(execpath :commands_rust)",
        "fi_ibex_commands_loc": "$(execpath :fi_ibex_commands_rust)",
        "pentest_lib_commands_loc": "$(execpath :pentest_lib_commands_rust)",
    },
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:arrayvec",
        "@crate_index//:serde",
        "@crate_index//:strum",
    ],
)
