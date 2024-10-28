# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_library")
load("//sw/device/silicon_creator/manuf/base:provisioning_inputs.bzl", "EARLGREY_SKUS")

package(default_visibility = ["//visibility:public"])

[
    rust_library(
        name = "ft_lib_{}".format(sku),
        srcs = ["src/lib.rs"],
        crate_name = "ft_lib",
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
        ] + config["host_ext_libs"],
    )
    for sku, config in EARLGREY_SKUS.items()
]
