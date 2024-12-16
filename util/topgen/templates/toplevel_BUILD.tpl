# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
${gencmd}

<%
top_name = "top_" + top["name"]
%>\
load("//rules:linker.bzl", "ld_library")

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
)

ld_library(
    name = "${top_name}_memory",
    includes = ["${top_name}_memory.ld"],
)
