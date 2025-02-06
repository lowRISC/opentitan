# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
${gencmd}

<%
top_name = top["name"]

all_ips = {}
for m in sorted(top["module"], key=lambda x: x["type"]):
    all_ips[m["type"]] = m.get("attr", "")

%>\
load("//rules/opentitan:hw.bzl", "opentitan_top")
% for (ip, type) in all_ips.items():
%   if type == "ipgen":
load("//hw/top_${top_name}/ip_autogen/${ip}:defs.bzl", "${ip.upper()}")
%   elif type == "reggen_top" or type == "reggen_only":
load("//hw/top_${top_name}/ip/${ip}:defs.bzl", "${ip.upper()}")
%   else:
load("//hw/ip/${ip}:defs.bzl", "${ip.upper()}")
%   endif:
% endfor

${top_name.upper()} = opentitan_top(
    name = "${top_name}",
    hjson = "//hw/top_${top_name}/data/autogen:top_${top_name}.gen.hjson",
    top_lib = "//hw/top_${top_name}/sw/autogen:top_${top_name}",
    top_ld = "//hw/top_${top_name}/sw/autogen:top_${top_name}_memory",
    ips = [
% for ip in all_ips.keys():
        ${ip.upper()},
% endfor
    ],
)
