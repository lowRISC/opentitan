# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_doc", "rust_library", "rust_test")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "dediprog",
    srcs = [
        "src/gpio.rs",
        "src/lib.rs",
        "src/spi.rs",
    ],
    compile_data = glob(["config/*.json5"]),
    crate_name = "ot_transport_dediprog",
    deps = [
        "//sw/host/opentitanlib:opentitanlib_base",
        "@crate_index//:anyhow",
        "@crate_index//:log",
        "@crate_index//:regex",
        "@crate_index//:rusb",
    ],
)

rust_doc(
    name = "dediprog_doc",
    crate = ":dediprog",
)

rust_test(
    name = "dediprog_test",
    crate = ":dediprog",
)
