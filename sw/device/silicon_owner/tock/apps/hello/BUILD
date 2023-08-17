# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")
load("//rules:opentitan.bzl", "OPENTITAN_CPU")
load("//rules:tock.bzl", "tock_elf2tab", "tock_image")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "hello",
    srcs = [
        "src/hello.rs",
    ],
    # We specifically restrict our build target to the OpenTitan
    # CPU because libtock does not support an x86_64 target.
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/silicon_owner/tock/apps:single_app_layout",
        "@libtock",
    ],
)

tock_elf2tab(
    name = "tab",
    src = ":hello",
    arch = "rv32imc",
)

tock_image(
    name = "image",
    app_flash_start = 0x20040000,
    apps = [":tab"],
    kernel = "//sw/device/silicon_owner/tock/kernel",
)
