# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")
load("@rules_rust//bindgen:defs.bzl", "rust_bindgen_library")

package(default_visibility = ["//visibility:public"])

rust_bindgen_library(
    name = "xmodem_testlib",
    bindgen_flags = [
        "--allowlist-function=xmodem_.*",
    ],
    cc_lib = "//sw/device/silicon_creator/lib:xmodem_testlib",
    header = "//sw/device/silicon_creator/lib:xmodem_testlib.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
        "--allow=non_camel_case_types",
    ],
)

rust_library(
    name = "xmodem",
    srcs = [
        "xmodem.rs",
    ],
    deps = [
        ":xmodem_testlib",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:log",
        "@crate_index//:serde",
    ],
)

rust_test(
    name = "lrzsz_test",
    srcs = [
        "lrzsz_test.rs",
    ],
    deps = [
        ":xmodem",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
    ],
)
