# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "string_flag")

package(default_visibility = ["//visibility:public"])

string_flag(
    name = "kernel",
    build_setting_default = "downstream",
    values = [
        "downstream",
        "upstream",
    ],
)

config_setting(
    name = "upstream_kernel",
    flag_values = {":kernel": "upstream"},
)

alias(
    name = "test_kernel_silicon",
    actual = "//sw/device/silicon_owner/tock/kernel:kernel_silicon",
)

alias(
    name = "test_kernel_fpga",
    actual = select({
        ":upstream_kernel": "//sw/device/silicon_owner/tock/upstream_kernel:kernel",
        "//conditions:default": "//sw/device/silicon_owner/tock/kernel:kernel_fpga",
    }),
)
