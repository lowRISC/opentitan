# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@rules_rust//crate_universe:defs.bzl", "crate", "crates_vendor")

crates_vendor(
    name = "crate_index",
    annotations = {
        "libudev-sys": [crate.annotation(
            patch_args = ["-p1"],
            patches = ["@//third_party/rust/patches:libudev-sys-0.1.4.patch"],
        )],
    },
    cargo_lockfile = "//third_party/rust:Cargo.lock",
    manifests = ["//third_party/rust:Cargo.toml"],
    mode = "remote",
    tags = ["manual"],
    vendor_path = "crates",
)
