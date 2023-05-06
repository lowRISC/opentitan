# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "openocd_test",
    srcs = [
        "src/openocd_test.rs",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen/chip:top_earlgrey",
        "//sw/host/opentitanlib",
        "//third_party/rust/crates:regex",
        "@crate_index//:anyhow",
        "@crate_index//:humantime",
        "@crate_index//:lazy_static",
        "@crate_index//:log",
        "@crate_index//:serde_json",
        "@crate_index//:structopt",
    ],
)

rust_binary(
    name = "openocd_ila_stress_test",
    srcs = [
        "src/openocd_ila_stress_test.rs",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen/chip:top_earlgrey",
        "//sw/host/opentitanlib",
        "//third_party/rust/crates:regex",
        "@crate_index//:anyhow",
        "@crate_index//:humantime",
        "@crate_index//:lazy_static",
        "@crate_index//:log",
        "@crate_index//:serde_json",
        "@crate_index//:structopt",
    ],
)

rust_binary(
    name = "sram_load",
    srcs = [
        "src/sram_load.rs",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen/chip:top_earlgrey",
        "//sw/host/opentitanlib",
        "//third_party/rust/crates:regex",
        "@crate_index//:anyhow",
        "@crate_index//:humantime",
        "@crate_index//:lazy_static",
        "@crate_index//:log",
        "@crate_index//:serde_json",
        "@crate_index//:structopt",
    ],
)
