# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")
load(
    "//sw/device/silicon_creator/manuf/base:provisioning_inputs.bzl",
    "EARLGREY_SKUS",
)

package(default_visibility = ["//visibility:public"])

[
    rust_binary(
        name = "ft_{}".format(sku),
        srcs = ["src/main.rs"],
        deps = [
            "//sw/host/opentitanlib",
            "//sw/host/provisioning/ft_lib:ft_lib_{}".format(sku),
            "//sw/host/provisioning/cert_lib",
            "//sw/host/provisioning/ujson_lib",
            "//sw/host/provisioning/util_lib",
            "@crate_index//:anyhow",
            "@crate_index//:clap",
            "@crate_index//:elliptic-curve",
            "@crate_index//:humantime",
            "@crate_index//:log",
            "@crate_index//:p256",
            "@lowrisc_serde_annotate//serde_annotate",
        ],
    )
    for sku in EARLGREY_SKUS.keys()
]

filegroup(
    name = "ft_all",
    srcs = [
        ":ft_{}".format(sku)
        for sku in EARLGREY_SKUS.keys()
    ],
)
