# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")
load(
    "//sw/device/silicon_creator/manuf/base:provisioning_inputs.bzl",
    "FT_PERSONALIZE_ENDORSEMENT_KEYS",
)

package(default_visibility = ["//visibility:public"])

# Additional data dependencies on this rust binary allow the provisioning
# orchestration scripts to invoke this binary with bazel run.
rust_binary(
    name = "ft",
    testonly = True,
    srcs = ["src/main.rs"],
    data = [
        "//sw/device/silicon_creator/manuf/base:ft_personalize_all",
        "//sw/device/silicon_creator/manuf/base:sram_ft_individualize_all",
        "//third_party/openocd:jtag_cmsis_dap_adapter_cfg",
        "//third_party/openocd:jtag_olimex_cfg",
        "//third_party/openocd:openocd_bin",
    ] + FT_PERSONALIZE_ENDORSEMENT_KEYS,
    deps = [
        "//sw/host/opentitanlib",
        "//sw/host/provisioning/ft_lib",
        "//sw/host/provisioning/ujson_lib",
        "//sw/host/provisioning/util_lib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
    ],
)
