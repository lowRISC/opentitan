# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "bad_rom_ext_signature",
    srcs = [
        "src/main.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "//third_party/rust/crates:anyhow",
        "//third_party/rust/crates:humantime",
        "//third_party/rust/crates:regex",
        "//third_party/rust/crates:structopt",
        "//third_party/rust/crates:tempfile",
    ],
)

filegroup(
    name = "test_resources",
    srcs = [
        ":bad_rom_ext_signature",
    ],
)
