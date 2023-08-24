# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:autogen.bzl", "autogen_hjson_header")

package(default_visibility = ["//visibility:public"])

autogen_hjson_header(
    name = "soc_proxy_regs",
    srcs = [
        "soc_proxy.hjson",
    ],
)

filegroup(
    name = "all_files",
    srcs = glob(["**"]),
)
