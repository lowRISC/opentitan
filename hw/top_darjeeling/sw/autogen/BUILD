# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:linker.bzl", "ld_library")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "top_earlgrey",
    srcs = [
        "top_earlgrey.c",
    ],
    hdrs = [
        "top_earlgrey.h",
        "top_earlgrey_memory.h",
    ],
)

ld_library(
    name = "top_earlgrey_memory",
    includes = ["top_earlgrey_memory.ld"],
)

filegroup(
    name = "all_files",
    srcs = glob(["**"]),
)
