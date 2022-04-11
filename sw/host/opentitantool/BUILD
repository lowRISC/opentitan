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
        "//third_party/cargo:anyhow",
        "//third_party/cargo:directories",
        "//third_party/cargo:env_logger",
        "//third_party/cargo:erased_serde",
        "//third_party/cargo:hex",
        "//third_party/cargo:humantime",
        "//third_party/cargo:indicatif",
        "//third_party/cargo:log",
        "//third_party/cargo:nix",
        "//third_party/cargo:raw_tty",
        "//third_party/cargo:regex",
        "//third_party/cargo:serde",
        "//third_party/cargo:serde_json",
        "//third_party/cargo:shellwords",
        "//third_party/cargo:structopt",
        "//third_party/cargo:thiserror",
    ],
)

filegroup(
    name = "test_resources",
    srcs = [
        ":opentitantool",
        "//sw/host/opentitantool/config",
    ],
)
