# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@rules_rust//crate_universe:defs.bzl", "crate", "crates_vendor")

crates_vendor(
    name = "tock_index",
    cargo_lockfile = "//third_party/tock:Cargo.lock",
    manifests = ["//third_party/tock:Cargo.toml"],
    mode = "remote",
    tags = ["manual"],
    vendor_path = "crates",
)
