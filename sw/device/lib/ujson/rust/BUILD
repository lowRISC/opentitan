# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_test")
load("//rules:ujson.bzl", "ujson_rust")

package(default_visibility = ["//visibility:public"])

ujson_rust(
    name = "example",
    srcs = ["//sw/device/lib/ujson:example"],
)

rust_test(
    name = "roundtrip_test",
    srcs = [
        "roundtrip_test.rs",
    ],
    compile_data = [
        ":example",
    ],
    data = ["//sw/device/lib/ujson:example_roundtrip"],
    env = {
        "ROUNDTRIP_CLIENT": "$(rootpath //sw/device/lib/ujson:example_roundtrip)",
        "RUST_BACKTRACE": "1",
    },
    rustc_env = {
        "example": "$(location :example)",
    },
    deps = [
        "//sw/host/opentitanlib",
        "//third_party/rust/crates:anyhow",
        "//third_party/rust/crates:serde",
        "//third_party/rust/crates:serde_json",
    ],
)
