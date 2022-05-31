# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "rom_ext_signer",
    srcs = [
        "src/main.rs",
    ],
    deps = [
        "//sw/host/rom_ext_image_tools/signer/image:rom_ext_image",
        "//third_party/rust/crates:anyhow",
        "//third_party/rust/crates:object",
        "//third_party/rust/crates:thiserror",
        "//third_party/rust/crates:zerocopy",
        "@mundane",
    ],
)
