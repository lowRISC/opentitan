# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")
load("//third_party/cargo:crates.bzl", "all_crate_deps")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "rom_ext_image",
    srcs = [
        "src/image.rs",
        "src/lib.rs",
        "src/manifest.rs",
    ],
    deps = all_crate_deps(),
)

rust_test(
    name = "rom_ext_image_test",
    crate = ":rom_ext_image",
)
