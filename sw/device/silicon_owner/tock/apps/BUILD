# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:linker.bzl", "ld_library")

package(default_visibility = ["//visibility:public"])

ld_library(
    name = "single_app_layout",
    includes = ["@libtock//build_scripts:layout"],
    script = "single_app_layout.ld",
)
