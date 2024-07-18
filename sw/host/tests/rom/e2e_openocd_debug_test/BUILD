# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "asm_interrupt_handler",
    srcs = [
        "src/asm_interrupt_handler.rs",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen/chip:top_earlgrey",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:regex",
    ],
)

rust_binary(
    name = "shutdown_execution_asm",
    srcs = [
        "src/shutdown_execution_asm.rs",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen/chip:top_earlgrey",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:regex",
    ],
)

rust_binary(
    name = "asm_watchdog_bark",
    srcs = [
        "src/asm_watchdog_bark.rs",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen/chip:top_earlgrey",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:regex",
    ],
)

rust_binary(
    name = "asm_watchdog_bite",
    srcs = [
        "src/asm_watchdog_bite.rs",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen/chip:top_earlgrey",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:regex",
    ],
)

rust_binary(
    name = "debug_test",
    srcs = [
        "src/debug_test.rs",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen/chip:top_earlgrey",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:regex",
    ],
)
