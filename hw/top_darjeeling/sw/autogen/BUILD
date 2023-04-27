# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:linker.bzl", "ld_library")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "top_darjeeling",
    srcs = [
        "top_darjeeling.c",
    ],
    hdrs = [
        "top_darjeeling.h",
        "top_darjeeling_memory.h",
    ],
)

ld_library(
    name = "top_darjeeling_memory",
    includes = ["top_darjeeling_memory.ld"],
)

filegroup(
    name = "all_files",
    srcs = glob(["**"]),
)
