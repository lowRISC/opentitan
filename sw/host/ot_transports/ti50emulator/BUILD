# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_doc", "rust_library", "rust_test")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "ti50emulator",
    srcs = [
        "src/emu.rs",
        "src/gpio.rs",
        "src/i2c.rs",
        "src/lib.rs",
        "src/uart.rs",
    ],
    compile_data = glob(["config/*.json5"]),
    crate_name = "ot_transport_ti50emulator",
    deps = [
        "//sw/host/opentitanlib:opentitanlib_base",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:log",
        "@crate_index//:rustix",
        "@crate_index//:serde",
        "@crate_index//:serde_json",
        "@crate_index//:tokio",
    ],
)

rust_doc(
    name = "ti50emulator_doc",
    crate = ":ti50emulator",
)

rust_test(
    name = "ti50emulator_test",
    crate = ":ti50emulator",
)
