# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_doc", "rust_library", "rust_test")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "chipwhisperer",
    srcs = [
        "src/board.rs",
        "src/gpio.rs",
        "src/lib.rs",
        "src/spi.rs",
        "src/usb.rs",
    ],
    compile_data = glob(["config/*.json5"]),
    crate_name = "ot_transport_chipwhisperer",
    deps = [
        "//sw/host/opentitanlib:opentitanlib_base",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:erased-serde",
        "@crate_index//:log",
        "@crate_index//:regex",
        "@crate_index//:rusb",
        "@crate_index//:serde",
        "@crate_index//:serialport",
        "@crate_index//:zerocopy",
    ],
)

rust_doc(
    name = "chipwhisperer_doc",
    crate = ":chipwhisperer",
)

rust_test(
    name = "chipwhisperer_test",
    crate = ":chipwhisperer",
)
