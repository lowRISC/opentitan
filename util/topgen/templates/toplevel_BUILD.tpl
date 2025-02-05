# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
${gencmd}

<%
top_name = "top_" + top["name"]
%>\
load("//rules:linker.bzl", "ld_library")
load("//hw/top:defs.bzl", "opentitan_require_top")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "${top_name}",
    srcs = [
        "${top_name}.c",
    ],
    hdrs = [
        "${top_name}.h",
        "${top_name}_memory.h",
    ],
    defines = ["OPENTITAN_IS_${top["name"].upper()}"],
    target_compatible_with = opentitan_require_top("${top["name"]}"),
)

ld_library(
    name = "${top_name}_memory",
    defines = [
        "OPENTITAN_TOP_MEMORY_LD=${top_name}_memory.ld",
        "OPENTITAN_IS_${top["name"].upper()}",
    ],
    includes = ["${top_name}_memory.ld"],
    target_compatible_with = opentitan_require_top("${top["name"]}"),
)
