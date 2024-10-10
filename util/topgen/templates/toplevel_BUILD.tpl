# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
${gencmd.replace("//", "#")}

<%
top_name = "top_" + top["name"]
%>\
load("//rules:linker.bzl", "ld_library")
load("//rules:autogen.bzl", "autogen_top_dt")

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

# This macro will generate two targets:
# - dt_api: this is a library that all DT-headers depends on
# - devicetables: this is the DT library that contains the top tables.
autogen_top_dt(
    topname = "${top_name}",
    # Top cfg.
    top_gen_cfg = "${topgencfg}",
    # IP to hjson map.
    ip_to_hjson = {
    % for (ip, label) in sorted(name_to_hjson.items(), key=lambda x: x[0]):
        "${label}": "${ip}",
    % endfor
    },
    # Toplevel library.
    top_lib = ":${top_name}",
    # DT IP headers: we point to a target that has to be manually created at the moment.
    dt_ip_deps = ["//hw/${top_name}:dt_headers"],
)

filegroup(
    name = "all_files",
    srcs = glob(["**"]),
)
