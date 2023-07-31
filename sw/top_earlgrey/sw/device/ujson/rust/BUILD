# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_test")

package(default_visibility = ["//visibility:public"])

rust_test(
    name = "roundtrip_test",
    srcs = [
        "//sw/lib/sw/device/ujson/rust:roundtrip_test",
    ],
    compile_data = [
        "//sw/lib/sw/device/ujson/rust:example",
    ],
    data = ["//sw/top_earlgrey/sw/device/ujson:example_roundtrip"],
    env = {
        "ROUNDTRIP_CLIENT": "$(rootpath //sw/top_earlgrey/sw/device/ujson:example_roundtrip)",
        "RUST_BACKTRACE": "1",
    },
    rustc_env = {
        "example": "$(location //sw/lib/sw/device/ujson/rust:example)",
    },
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:arrayvec",
        "@crate_index//:serde",
        "@crate_index//:serde_json",
    ],
)
