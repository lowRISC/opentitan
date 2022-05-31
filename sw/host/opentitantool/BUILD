# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "opentitantool",
    srcs = [
        "src/command/bootstrap.rs",
        "src/command/console.rs",
        "src/command/emulator.rs",
        "src/command/gpio.rs",
        "src/command/hello.rs",
        "src/command/i2c.rs",
        "src/command/image.rs",
        "src/command/load_bitstream.rs",
        "src/command/mod.rs",
        "src/command/set_pll.rs",
        "src/command/spi.rs",
        "src/command/version.rs",
        "src/main.rs",
    ],
    proc_macro_deps = [
        "//sw/host/opentitanlib/opentitantool_derive",
    ],
    stamp = 1,
    deps = [
        "//sw/host/opentitanlib",
        "//third_party/rust/crates:anyhow",
        "//third_party/rust/crates:directories",
        "//third_party/rust/crates:env_logger",
        "//third_party/rust/crates:erased_serde",
        "//third_party/rust/crates:hex",
        "//third_party/rust/crates:humantime",
        "//third_party/rust/crates:indicatif",
        "//third_party/rust/crates:log",
        "//third_party/rust/crates:nix",
        "//third_party/rust/crates:raw_tty",
        "//third_party/rust/crates:regex",
        "//third_party/rust/crates:serde",
        "//third_party/rust/crates:serde_json",
        "//third_party/rust/crates:shellwords",
        "//third_party/rust/crates:structopt",
        "//third_party/rust/crates:thiserror",
    ],
)

filegroup(
    name = "test_resources",
    srcs = [
        ":opentitantool",
        "//sw/host/opentitantool/config",
    ],
)
