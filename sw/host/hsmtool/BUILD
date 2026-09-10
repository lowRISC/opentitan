# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//pkg:mappings.bzl", "pkg_attributes", "pkg_filegroup", "pkg_files")

package(default_visibility = ["//visibility:public"])

pkg_files(
    name = "binary",
    srcs = ["@opentitan_signing_infra//hsmtool"],
    attributes = pkg_attributes(mode = "0755"),
)

pkg_filegroup(
    name = "package",
    srcs = [
        ":binary",
    ],
    prefix = "hsmtool",
)
