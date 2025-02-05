# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------#
# PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
# util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson
# -o hw/top_darjeeling

load("//rules:linker.bzl", "ld_library")
load("//hw/top:defs.bzl", "opentitan_require_top")

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
    defines = ["OPENTITAN_IS_DARJEELING"],
    target_compatible_with = opentitan_require_top("darjeeling"),
)

ld_library(
    name = "top_darjeeling_memory",
    defines = [
        "OPENTITAN_TOP_MEMORY_LD=top_darjeeling_memory.ld",
        "OPENTITAN_IS_DARJEELING",
    ],
    includes = ["top_darjeeling_memory.ld"],
    target_compatible_with = opentitan_require_top("darjeeling"),
)
