# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:linker.bzl", "ld_library")

package(default_visibility = ["//visibility:public"])

ld_library(
    name = "libtock_layout",
    includes = [
        "@libtock//build_scripts:layout",
    ],
)

ld_library(
    name = "single_app_layout",
    script = "single_app_layout.ld",
    deps = [
        ":libtock_layout",
    ],
)
