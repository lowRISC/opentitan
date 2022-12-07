# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")
load("@rules_pkg//pkg:mappings.bzl", "pkg_filegroup", "pkg_files")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "tpm2-test-server",
    srcs = [
        "src/interface.rs",
        "src/main.rs",
    ],
    proc_macro_deps = [
        "//sw/host/opentitanlib/opentitantool_derive",
    ],
    stamp = 1,
    deps = [
        "//sw/host/opentitanlib",
        "//third_party/rust/crates:anyhow",
        "//third_party/rust/crates:env_logger",
        "//third_party/rust/crates:log",
        "//third_party/rust/crates:mio",
        "//third_party/rust/crates:num_enum",
        "//third_party/rust/crates:structopt",
    ],
)

pkg_files(
    name = "binary",
    srcs = [":tpm2-test-server"],
)

pkg_filegroup(
    name = "package",
    srcs = [
        ":binary",
    ],
    prefix = "tpm2-test-server",
)
