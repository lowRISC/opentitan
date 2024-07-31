# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "cp",
    testonly = True,
    srcs = ["src/main.rs"],
    data = [
        "//sw/device/silicon_creator/manuf/base:sram_cp_provision",
        "//third_party/openocd:jtag_cmsis_dap_adapter_cfg",
        "//third_party/openocd:jtag_olimex_cfg",
        "//third_party/openocd:openocd_bin",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "//sw/host/provisioning/cp_lib",
        "//sw/host/provisioning/ujson_lib",
        "//sw/host/provisioning/util_lib",
        "@crate_index//:anyhow",
        "@crate_index//:arrayvec",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:tiny-keccak",
    ],
)
