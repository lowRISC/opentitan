# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_library")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "default_ft_ext_lib",
    srcs = ["src/main.rs"],
    crate_name = "ft_ext_lib",
    edition = "2024",
    deps = [
        "@crate_index//:anyhow",
        "@crate_index//:arrayvec",
        "@lowrisc_opentitan//sw/host/provisioning/perso_tlv_lib",
        "@lowrisc_opentitan//sw/host/provisioning/util_lib",
    ],
)
