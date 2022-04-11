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
        "//third_party/cargo:anyhow",
        "//third_party/cargo:object",
        "//third_party/cargo:thiserror",
        "//third_party/cargo:zerocopy",
        "@mundane",
    ],
)
