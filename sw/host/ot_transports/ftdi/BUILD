# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_doc", "rust_library", "rust_test")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "ftdi",
    srcs = [
        "src/chip.rs",
        "src/gpio.rs",
        "src/lib.rs",
        "src/spi.rs",
    ],
    compile_data = glob(["config/*.json5"]),
    crate_name = "ot_transport_ftdi",
    deps = [
        "//sw/host/opentitanlib:opentitanlib_base",
        "@crate_index//:anyhow",
        "@crate_index//:embedded-hal",
        "@crate_index//:ftdi",
        "@crate_index//:ftdi-embedded-hal",
        "@crate_index//:log",
        "@crate_index//:serialport",
    ],
)

rust_doc(
    name = "ftdi_doc",
    crate = ":ftdi",
)

rust_test(
    name = "ftdi_test",
    crate = ":ftdi",
)
