# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_doc", "rust_library", "rust_test")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "verilator",
    srcs = [
        "src/gpio.rs",
        "src/lib.rs",
        "src/subprocess.rs",
        "src/transport.rs",
    ],
    compile_data = glob(["config/*.json5"]),
    crate_name = "ot_transport_verilator",
    deps = [
        "//sw/host/opentitanlib:opentitanlib_base",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:erased-serde",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:regex",
        "@crate_index//:serde",
    ],
)

rust_doc(
    name = "verilator_doc",
    crate = ":verilator",
)

rust_test(
    name = "verilator_test",
    crate = ":verilator",
)
