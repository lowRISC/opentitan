# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@provisioning_exts//:cfg.bzl", "HOST_FT_EXTS")
load("@rules_rust//rust:defs.bzl", "rust_library")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "ft_lib",
    srcs = ["src/lib.rs"],
    deps = [
        "//sw/host/opentitanlib",
        "//sw/host/ot_certs",
        "//sw/host/provisioning/cert_lib",
        "//sw/host/provisioning/perso_tlv_lib",
        "//sw/host/provisioning/perso_tlv_lib:perso_tlv_objects",
        "//sw/host/provisioning/ujson_lib",
        "//sw/host/provisioning/util_lib",
        "@crate_index//:anyhow",
        "@crate_index//:arrayvec",
        "@crate_index//:clap",
        "@crate_index//:elliptic-curve",
        "@crate_index//:hex",
        "@crate_index//:log",
        "@crate_index//:p256",
        "@crate_index//:serde",
        "@crate_index//:serde_json",
        "@crate_index//:sha2",
        "@crate_index//:zerocopy",
    ] + HOST_FT_EXTS,
)
