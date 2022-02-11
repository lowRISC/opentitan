# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")
load("//third_party/cargo:crates.bzl", "all_crate_deps")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "opentitantool",
    srcs = [
        "src/command/bootstrap.rs",
        "src/command/console.rs",
        "src/command/gpio.rs",
        "src/command/hello.rs",
        "src/command/i2c.rs",
        "src/command/image.rs",
        "src/command/load_bitstream.rs",
        "src/command/mod.rs",
        "src/command/spi.rs",
        "src/main.rs",
    ],
    proc_macro_deps = [
        "//sw/host/opentitanlib/opentitantool_derive",
    ],
    deps = [
        "//sw/host/opentitanlib",
    ] + all_crate_deps(),
)

filegroup(
    name = "test_resources",
    srcs = [
        ":opentitantool",
        "//sw/host/opentitantool/config",
    ],
)
