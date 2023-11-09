# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules/opentitan:toolchain.bzl", "LOCALTOOLS_TOOLCHAIN", "localtools_toolchain")

localtools_toolchain(
    name = "localtools_impl",
)

toolchain_type(
    name = "localtools_type",
)

toolchain(
    name = "localtools",
    toolchain = ":localtools_impl",
    toolchain_type = LOCALTOOLS_TOOLCHAIN,
)
