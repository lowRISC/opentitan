# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load(
    "//rules:autogen.bzl",
    "autogen_hjson_sw_headers",
)

autogen_hjson_sw_headers(
    name_prefix = "flash_ctrl",
    srcs = [
        "data/flash_ctrl.hjson",
    ],
    node = "core",
)


filegroup(
    name = "all_files",
    srcs = glob(["**"]),
)
