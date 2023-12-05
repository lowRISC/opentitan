# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "ft",
    testonly = True,
    srcs = ["src/main.rs"],
    data = [
        "//sw/device/silicon_creator/manuf/skus/earlgrey_a0/sival_bringup:ft_personalize_1",
        "//sw/device/silicon_creator/manuf/skus/earlgrey_a0/sival_bringup:ft_personalize_2",
        "//sw/device/silicon_creator/manuf/skus/earlgrey_a0/sival_bringup:ft_personalize_3",
        "//sw/device/silicon_creator/manuf/skus/earlgrey_a0/sival_bringup:sram_ft_individualize_all",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "//sw/host/provisioning/ft_lib",
        "//sw/host/provisioning/ujson_lib",
        "//sw/host/provisioning/util_lib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
    ],
)
